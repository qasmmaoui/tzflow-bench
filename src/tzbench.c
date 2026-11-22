/*
 * tzbench.c - Normal-world ARM64 micro-benchmarks for TZ-Flow.
 *
 * What this program measures (all on the CPU it runs on, nothing estimated):
 *   E3  sweep time of the Proposition 1 consistency check vs cache size |C|
 *   E3b correctness: false positives on an untouched cache (must be 0)
 *   E4a detection of redirected cache entries (action rewritten)
 *   E4b detection of widened cache entries (mask bits cleared), split into
 *       harmful widenings (some packet now gets a wrong action) and harmless ones
 *   E5  detection probability of random sampling (sample size s, k tampered entries)
 *   D1  incremental multiset digest: cost of one rule add/remove, and of a full recompute
 *
 * What it does NOT measure: anything inside the TrustZone secure world
 * (world switches, OP-TEE overhead). Those need a TrustZone-capable platform.
 *
 * Model
 *   Header key = 2 x 64-bit words:
 *     w0 = ip_src(32) << 32 | ip_dst(32)
 *     w1 = in_port(16) << 48 | eth_type(16) << 32 | ip_proto(8) << 24 | tp_dst(16) << 8
 *   Rule  = (value, mask, priority, action). Higher priority wins.
 *   Lookup with un-wildcarding: for every rule examined that does NOT match,
 *   one witness bit (a masked bit where key and rule differ) is added to U;
 *   for the matching rule its whole mask is added to U. Any packet agreeing
 *   with the key on U takes the same decision path (Proposition 1).
 *   Megaflow = (key & U, U, action), built on cache misses as OVS does.
 */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <openssl/evp.h>

typedef struct { uint64_t w[2]; } key_t2;
typedef struct { key_t2 v, m; int prio; uint32_t act; } rule_t;
typedef struct { key_t2 k, m; uint32_t act; } mflow_t;

/* ---------------- RNG (xoshiro256**) ---------------- */
static uint64_t s_[4];
static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static uint64_t rnd(void) {
    uint64_t r = rotl(s_[1] * 5, 7) * 9, t = s_[1] << 17;
    s_[2] ^= s_[0]; s_[3] ^= s_[1]; s_[1] ^= s_[2]; s_[0] ^= s_[3]; s_[2] ^= t; s_[3] = rotl(s_[3], 45);
    return r;
}
static void seed(uint64_t x) { for (int i = 0; i < 4; i++) { x += 0x9e3779b97f4a7c15ULL; uint64_t z = x; z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL; s_[i] = z ^ (z >> 31); } }
static uint32_t rndu(uint32_t n) { return (uint32_t)(rnd() % n); }

static double now_s(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }

/* ---------------- field helpers ---------------- */
#define IPDST_M  0x00000000FFFFFFFFULL
#define IPSRC_M  0xFFFFFFFF00000000ULL
#define INPORT_M 0xFFFF000000000000ULL
#define ETH_M    0x0000FFFF00000000ULL
#define PROTO_M  0x00000000FF000000ULL
#define TPDST_M  0x0000000000FFFF00ULL

static uint64_t prefix32(int len) { return len == 0 ? 0 : (0xFFFFFFFFULL << (32 - len)) & 0xFFFFFFFFULL; }

/* Generate a realistic mixed rule set: ACLs (proto + port + dst prefix),
 * forwarding by dst prefix, a few in_port rules, and a default rule. */
static uint32_t gen_pool_dst[64];
static void gen_rules(rule_t *r, int n, int nports) {
    for (int i = 0; i < 64; i++) gen_pool_dst[i] = (uint32_t)rnd();
    for (int i = 0; i < n - 1; i++) {
        rule_t *x = &r[i]; memset(x, 0, sizeof *x);
        uint32_t base = gen_pool_dst[rndu(64)] ^ ((uint32_t)rnd() & 0x0000FFFF);
        int kind = rndu(100);
        x->m.w[1] |= ETH_M; x->v.w[1] |= 0x0800ULL << 32;               /* IPv4 */
        if (kind < 50) {                                                /* forwarding by dst prefix */
            int len = 8 + rndu(25);
            x->m.w[0] |= prefix32(len); x->v.w[0] |= base & prefix32(len);
            x->prio = 100 + len;
        } else if (kind < 85) {                                         /* ACL */
            int len = 16 + rndu(17);
            static const uint16_t ports[] = {22, 23, 25, 53, 80, 123, 161, 443, 445, 3389, 8080};
            x->m.w[0] |= prefix32(len); x->v.w[0] |= base & prefix32(len);
            x->m.w[1] |= PROTO_M | TPDST_M;
            x->v.w[1] |= ((uint64_t)(rndu(2) ? 6 : 17) << 24) | ((uint64_t)ports[rndu(11)] << 8);
            if (rndu(2)) { int sl = 8 + rndu(17); x->m.w[0] |= prefix32(sl) << 32; x->v.w[0] |= ((uint64_t)((uint32_t)rnd() & prefix32(sl))) << 32; }
            x->prio = 1000 + len;
        } else {                                                        /* in_port steering */
            x->m.w[1] |= INPORT_M; x->v.w[1] |= (uint64_t)(1 + rndu(nports)) << 48;
            int len = rndu(2) ? 0 : 8 + rndu(17);
            x->m.w[0] |= prefix32(len); x->v.w[0] |= base & prefix32(len);
            x->prio = 500 + len;
        }
        x->v.w[0] &= x->m.w[0]; x->v.w[1] &= x->m.w[1];
        x->act = rndu(10) == 0 ? 0 : 1 + rndu(nports);                  /* 0 = drop */
    }
    rule_t *d = &r[n - 1]; memset(d, 0, sizeof *d); d->prio = 0; d->act = 1; /* table-miss -> port 1 */
}
static int cmp_prio(const void *a, const void *b) { return ((const rule_t *)b)->prio - ((const rule_t *)a)->prio; }

/* Packet generator biased toward rule regions (as real traffic hits rules). */
static key_t2 gen_packet(const rule_t *r, int n, int nports) {
    key_t2 p; const rule_t *x = &r[rndu(n)];
    p.w[0] = rnd(); p.w[1] = rnd() & ~0xFFULL;
    p.w[0] = (p.w[0] & ~x->m.w[0]) | x->v.w[0];
    p.w[1] = (p.w[1] & ~x->m.w[1]) | x->v.w[1];
    p.w[1] = (p.w[1] & ~ETH_M) | (0x0800ULL << 32);
    if (!(x->m.w[1] & INPORT_M)) p.w[1] = (p.w[1] & ~INPORT_M) | ((uint64_t)(1 + rndu(nports)) << 48);
    if (!(x->m.w[1] & PROTO_M)) p.w[1] = (p.w[1] & ~PROTO_M) | ((uint64_t)(rndu(2) ? 6 : 17) << 24);
    return p;
}

/* ---------------- classifier with un-wildcarding ---------------- */
static inline uint64_t top_bit(uint64_t x) { return x ? (1ULL << (63 - __builtin_clzll(x))) : 0; }

/* Lookup k in priority-sorted rules. pref = mask in which witness bits are preferred
 * (all-ones when building megaflows; the entry's own mask when checking it). */
static uint32_t lookup(const rule_t *r, int n, key_t2 k, key_t2 pref, key_t2 *U) {
    U->w[0] = U->w[1] = 0;
    for (int i = 0; i < n; i++) {
        uint64_t d0 = (k.w[0] ^ r[i].v.w[0]) & r[i].m.w[0];
        uint64_t d1 = (k.w[1] ^ r[i].v.w[1]) & r[i].m.w[1];
        if (!d0 && !d1) { U->w[0] |= r[i].m.w[0]; U->w[1] |= r[i].m.w[1]; return r[i].act; }
        uint64_t p0 = d0 & pref.w[0], p1 = d1 & pref.w[1];
        if (p1) U->w[1] |= top_bit(p1);
        else if (p0) U->w[0] |= top_bit(p0);
        else if (d1) U->w[1] |= top_bit(d1);
        else U->w[0] |= top_bit(d0);
    }
    return 0; /* unreachable with a default rule */
}

/* ---------------- megaflow cache (tuple space: one hash table per mask) ---------------- */
typedef struct { key_t2 m; int cap, cnt; int32_t *slot; } tuple_t;
typedef struct { tuple_t *t; int nt, capt; mflow_t *e; int ne, cape; } cache_t;
static uint64_t hk(key_t2 k) { uint64_t h = k.w[0] * 0x9E3779B97F4A7C15ULL ^ (k.w[1] + 0x632BE59BD9B4E019ULL); h ^= h >> 29; h *= 0xBF58476D1CE4E5B9ULL; return h ^ (h >> 32); }
static int keq(key_t2 a, key_t2 b) { return a.w[0] == b.w[0] && a.w[1] == b.w[1]; }
static void cache_init(cache_t *c) { memset(c, 0, sizeof *c); }
static void cache_free(cache_t *c) { for (int i = 0; i < c->nt; i++) free(c->t[i].slot); free(c->t); free(c->e); }
static tuple_t *get_tuple(cache_t *c, key_t2 m) {
    for (int i = 0; i < c->nt; i++) if (keq(c->t[i].m, m)) return &c->t[i];
    if (c->nt == c->capt) { c->capt = c->capt ? 2 * c->capt : 16; c->t = realloc(c->t, c->capt * sizeof(tuple_t)); }
    tuple_t *t = &c->t[c->nt++]; t->m = m; t->cap = 64; t->cnt = 0; t->slot = malloc(64 * sizeof(int32_t));
    for (int i = 0; i < 64; i++) t->slot[i] = -1; return t;
}
static void tuple_put(cache_t *c, tuple_t *t, int idx);
static void tuple_grow(cache_t *c, tuple_t *t) {
    int32_t *old = t->slot; int oc = t->cap; t->cap *= 2; t->cnt = 0; t->slot = malloc(t->cap * sizeof(int32_t));
    for (int i = 0; i < t->cap; i++) t->slot[i] = -1;
    for (int i = 0; i < oc; i++) if (old[i] >= 0) tuple_put(c, t, old[i]);
    free(old);
}
static void tuple_put(cache_t *c, tuple_t *t, int idx) {
    if (2 * (t->cnt + 1) > t->cap) tuple_grow(c, t);
    uint64_t h = hk(c->e[idx].k) & (t->cap - 1);
    while (t->slot[h] >= 0) h = (h + 1) & (t->cap - 1);
    t->slot[h] = idx; t->cnt++;
}
static int cache_find(const cache_t *c, key_t2 p) {
    for (int i = 0; i < c->nt; i++) {
        const tuple_t *t = &c->t[i]; key_t2 mk = {{p.w[0] & t->m.w[0], p.w[1] & t->m.w[1]}};
        uint64_t h = hk(mk) & (t->cap - 1);
        while (t->slot[h] >= 0) { if (keq(c->e[t->slot[h]].k, mk)) return t->slot[h]; h = (h + 1) & (t->cap - 1); }
    }
    return -1;
}
/* Fill the cache with misses until it holds `target` megaflows. */
static void fill_cache(cache_t *c, const rule_t *r, int n, int nports, int target) {
    key_t2 all = {{~0ULL, ~0ULL}};
    c->cape = target; c->e = malloc(target * sizeof(mflow_t));
    long tries = 0;
    while (c->ne < target && tries < (long)target * 200) {
        tries++;
        key_t2 p = gen_packet(r, n, nports);
        if (cache_find(c, p) >= 0) continue;
        key_t2 U; uint32_t a = lookup(r, n, p, all, &U);
        mflow_t *m = &c->e[c->ne]; m->m = U; m->k.w[0] = p.w[0] & U.w[0]; m->k.w[1] = p.w[1] & U.w[1]; m->act = a;
        tuple_put(c, get_tuple(c, U), c->ne++);
    }
}

/* ---------------- Proposition 1 check ---------------- */
static int check_entry(const rule_t *r, int n, const mflow_t *e) {
    key_t2 U; uint32_t a = lookup(r, n, e->k, e->m, &U);
    return a == e->act && !(U.w[0] & ~e->m.w[0]) && !(U.w[1] & ~e->m.w[1]);
}
static long sweep(const rule_t *r, int n, const mflow_t *e, int ne) {
    long bad = 0; for (int i = 0; i < ne; i++) bad += !check_entry(r, n, &e[i]); return bad;
}

/* Ground truth for a widened entry: is there a packet inside it whose correct action differs? */
static int widening_harmful(const rule_t *r, int n, const mflow_t *e, int samples) {
    key_t2 all = {{~0ULL, ~0ULL}}, U;
    for (int s = 0; s < samples; s++) {
        key_t2 p = {{(rnd() & ~e->m.w[0]) | e->k.w[0], (rnd() & ~e->m.w[1]) | e->k.w[1]}};
        if (lookup(r, n, p, all, &U) != e->act) return 1;
    }
    return 0;
}

/* ---------------- multiset digest (LtHash16-style, SHAKE128 keyed) ---------------- */
#define LANES 1024
static unsigned char KEY[32];
static void elem_hash(const rule_t *x, uint16_t out[LANES]) {
    unsigned char buf[32 + 40]; memcpy(buf, KEY, 32);
    memcpy(buf + 32, &x->v, 16); memcpy(buf + 48, &x->m, 16); memcpy(buf + 64, &x->prio, 4); memcpy(buf + 68, &x->act, 4);
    EVP_MD_CTX *c = EVP_MD_CTX_new(); EVP_DigestInit_ex(c, EVP_shake128(), NULL);
    EVP_DigestUpdate(c, buf, sizeof buf); EVP_DigestFinalXOF(c, (unsigned char *)out, LANES * 2); EVP_MD_CTX_free(c);
}
static void dig_add(uint16_t d[LANES], const rule_t *x) { uint16_t h[LANES]; elem_hash(x, h); for (int i = 0; i < LANES; i++) d[i] += h[i]; }
static void dig_sub(uint16_t d[LANES], const rule_t *x) { uint16_t h[LANES]; elem_hash(x, h); for (int i = 0; i < LANES; i++) d[i] -= h[i]; }
static int table_digest_ok(const rule_t *r, int n, const uint16_t ref[LANES]) {
    uint16_t d[LANES] = {0}; for (int i = 0; i < n; i++) dig_add(d, &r[i]);
    return memcmp(d, ref, sizeof d) == 0;
}

/* ---------------- stats ---------------- */
static int cmpd(const void *a, const void *b) { double x = *(const double *)a, y = *(const double *)b; return (x > y) - (x < y); }
static void stats(double *v, int n, double *med, double *p5, double *p95) {
    qsort(v, n, sizeof(double), cmpd); *med = v[n / 2]; *p5 = v[(int)(0.05 * (n - 1))]; *p95 = v[(int)(0.95 * (n - 1))];
}

int main(int argc, char **argv) {
    int reps = argc > 1 ? atoi(argv[1]) : 30;
    const int nports = 48;
    const int RS[] = {100, 1000, 10000};
    const int CS[] = {100, 1000, 10000, 100000};
    for (int i = 0; i < 32; i++) KEY[i] = (unsigned char)(i * 37 + 11);
    seed(20261122);

    FILE *f3 = fopen("results/e3_sweep.csv", "w");
    FILE *f4 = fopen("results/e4_detection.csv", "w");
    FILE *f5 = fopen("results/e5_sampling.csv", "w");
    FILE *fd = fopen("results/d1_digest.csv", "w");
    if (!f3 || !f4 || !f5 || !fd) { perror("results/"); return 1; }
    fprintf(f3, "rules,cache_entries,tuples,median_ms,p5_ms,p95_ms,us_per_entry,false_positives\n");
    fprintf(f4, "rules,cache_entries,attack,injected,harmful,detected_harmful,flagged_harmless,tableonly_detected_harmful\n");
    fprintf(f5, "rules,cache_entries,tampered,sample_size,trials,detect_prob\n");
    fprintf(fd, "rules,op,median_us,p5_us,p95_us\n");

    double *t = malloc(sizeof(double) * (reps > 1000 ? reps : 1000));
    for (int ri = 0; ri < 3; ri++) {
        int n = RS[ri]; rule_t *r = malloc(n * sizeof(rule_t));
        gen_rules(r, n, nports); qsort(r, n, sizeof(rule_t), cmp_prio);

        /* D1: digest */
        uint16_t d[LANES] = {0};
        for (int k = 0; k < reps; k++) { double a = now_s(); memset(d, 0, sizeof d); for (int i = 0; i < n; i++) dig_add(d, &r[i]); t[k] = (now_s() - a) * 1e6; }
        { double m, a, b; stats(t, reps, &m, &a, &b); fprintf(fd, "%d,full_recompute,%.2f,%.2f,%.2f\n", n, m, a, b); }
        for (int k = 0; k < 1000; k++) { double a = now_s(); dig_add(d, &r[k % n]); t[k] = (now_s() - a) * 1e6; }
        { double m, a, b; stats(t, 1000, &m, &a, &b); fprintf(fd, "%d,add_one_rule,%.3f,%.3f,%.3f\n", n, m, a, b); }
        for (int k = 0; k < 1000; k++) { double a = now_s(); dig_sub(d, &r[k % n]); t[k] = (now_s() - a) * 1e6; }
        { double m, a, b; stats(t, 1000, &m, &a, &b); fprintf(fd, "%d,remove_one_rule,%.3f,%.3f,%.3f\n", n, m, a, b); }
        { /* tamper check: modify one rule's action; digest must differ */
            uint16_t d1[LANES] = {0}, d2[LANES] = {0}; for (int i = 0; i < n; i++) dig_add(d1, &r[i]);
            rule_t saved = r[n / 2]; r[n / 2].act ^= 1; for (int i = 0; i < n; i++) dig_add(d2, &r[i]); r[n / 2] = saved;
            fprintf(fd, "%d,tamper_detected,%d,,\n", n, memcmp(d1, d2, sizeof d1) != 0);
        }
        uint16_t dref[LANES] = {0}; for (int i = 0; i < n; i++) dig_add(dref, &r[i]);

        for (int ci = 0; ci < 4; ci++) {
            int target = CS[ci];
            if ((long)n * target > 400000000L) continue;   /* keep CI runs bounded */
            cache_t c; cache_init(&c); fill_cache(&c, r, n, nports, target);
            if (c.ne < target) { fprintf(stderr, "rules=%d: cache saturated at %d entries (target %d)\n", n, c.ne, target); }
            int ne = c.ne;
            /* E3 */
            long fp = 0;
            for (int k = 0; k < reps; k++) { double a = now_s(); fp = sweep(r, n, c.e, ne); t[k] = (now_s() - a) * 1e3; }
            { double m, a, b; stats(t, reps, &m, &a, &b); fprintf(f3, "%d,%d,%d,%.3f,%.3f,%.3f,%.3f,%ld\n", n, ne, c.nt, m, a, b, m * 1e3 / ne, fp); fflush(f3); }

            /* Baseline "table only" (protection of the OpenFlow table, as in
               enclave-based prior work): it raises an alarm iff the digest of the
               live rule table differs from the reference digest. Cache attacks
               below leave the table untouched; we still recompute and compare
               the digest after each attack so the baseline result is measured. */
            /* E4a: redirection */
            int inj = ne < 1000 ? ne / 10 : 100, det = 0, bdet = 0;
            for (int k = 0; k < inj; k++) {
                int i = rndu(ne); mflow_t e = c.e[i];
                uint32_t na; do na = rndu(nports + 1); while (na == e.act); e.act = na;
                det += !check_entry(r, n, &e);
                bdet += !table_digest_ok(r, n, dref);
            }
            fprintf(f4, "%d,%d,redirect,%d,%d,%d,0,%d\n", n, ne, inj, inj, det, bdet);
            /* E4b: widening (clear 1..8 random set bits of the mask) */
            int harm = 0, dh = 0, fh = 0, bdh = 0;
            for (int k = 0; k < inj; k++) {
                int i = rndu(ne); mflow_t e = c.e[i];
                int clears = 1 + rndu(8);
                for (int q = 0; q < clears; q++) {
                    int w = rndu(2); uint64_t mm = e.m.w[w]; if (!mm) { w ^= 1; mm = e.m.w[w]; } if (!mm) break;
                    int cnt = __builtin_popcountll(mm), pick = rndu(cnt);
                    for (int b = 0; b < 64; b++) if (mm >> b & 1) { if (!pick--) { e.m.w[w] &= ~(1ULL << b); e.k.w[w] &= ~(1ULL << b); break; } }
                }
                int h = widening_harmful(r, n, &e, 256), flagged = !check_entry(r, n, &e);
                harm += h; dh += h && flagged; fh += !h && flagged;
                bdh += h && !table_digest_ok(r, n, dref);
            }
            fprintf(f4, "%d,%d,widen,%d,%d,%d,%d,%d\n", n, ne, inj, harm, dh, fh, bdh);
            /* E4c: rule-table tampering (action of one non-default rule rewritten).
               Uses a separate RNG so that the other experiments are unchanged. */
            {
                uint64_t lcg = 0x5DEECE66DULL ^ (uint64_t)(n * 131 + ne);
                int tinj = inj, tdet = 0, tbdet = 0;
                for (int k = 0; k < tinj; k++) {
                    lcg = lcg * 6364136223846793005ULL + 1442695040888963407ULL;
                    int i = (int)((lcg >> 33) % (uint64_t)(n - 1));
                    rule_t saved = r[i];
                    r[i].act = (r[i].act + 1 + (uint32_t)((lcg >> 17) % nports)) % (nports + 1);
                    if (r[i].act == saved.act) r[i].act = (saved.act + 1) % (nports + 1);
                    int alarm = !table_digest_ok(r, n, dref);
                    tdet += alarm;      /* TZ-Flow: Reference Table digest vs controller digest */
                    tbdet += alarm;     /* table-only baseline uses the same digest check */
                    r[i] = saved;
                }
                fprintf(f4, "%d,%d,table_tamper,%d,%d,%d,0,%d\n", n, ne, tinj, tinj, tdet, tbdet);
            }
            fflush(f4);

            /* E5: sampling, k tampered among ne, sample size s (empirical) */
            const int KS[] = {1, 5, 20}; const double SF[] = {0.01, 0.05, 0.10, 0.25};
            if (ne >= 1000) for (int a = 0; a < 3; a++) for (int b = 0; b < 4; b++) {
                int kk = KS[a], s = (int)(SF[b] * ne), trials = 2000, hit = 0;
                char *bad = calloc(ne, 1);
                for (int tr = 0; tr < trials; tr++) {
                    memset(bad, 0, ne); for (int q = 0; q < kk; q++) bad[rndu(ne)] = 1;
                    int got = 0; for (int q = 0; q < s && !got; q++) got = bad[rndu(ne)];
                    hit += got;
                }
                free(bad);
                fprintf(f5, "%d,%d,%d,%d,%d,%.4f\n", n, ne, kk, s, trials, (double)hit / trials);
            }
            cache_free(&c);
        }
        free(r);
    }
    fclose(f3); fclose(f4); fclose(f5); fclose(fd); free(t);
    puts("done");
    return 0;
}
