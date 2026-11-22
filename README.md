# tzflow-bench

Normal-world ARM64 micro-benchmarks for **TZ-Flow** (flow table and datapath-cache attestation for SDN switches with ARM TrustZone).

The benchmark runs on GitHub-hosted `ubuntu-24.04-arm` runners. Every number in `results/` is measured on that CPU; nothing is estimated. The exact platform of each run is recorded in `results/platform.txt`.

## What is measured

| File | Experiment |
| --- | --- |
| `e3_sweep.csv` | Time to check every datapath-cache entry with Proposition 1, for 100 to 10 000 rules and 100 to 100 000 megaflows; false positives on an untouched cache (expected: 0) |
| `e4_detection.csv` | Detection of redirected entries (action rewritten) and widened entries (mask bits cleared), with widenings split into harmful and harmless |
| `e5_sampling.csv` | Empirical detection probability when only a random sample of entries is checked |
| `d1_digest.csv` | Cost of the incremental multiset digest (LtHash16-style, keyed SHAKE128): one rule add or remove, full recompute, tamper detection |

## What is not measured

Anything inside the TrustZone secure world: SMC world switches, OP-TEE trusted application overhead, secure storage. These runners are virtual machines without access to EL3. The checker code here is the same logic the trusted application would run, executed in the normal world.

## Model notes

- The classifier is a priority-ordered linear classifier with un-wildcarding: one witness bit per non-matching rule, the full mask of the matching rule. Megaflows are built on cache misses, as in Open vSwitch, and stored in a tuple-space cache (one hash table per mask).
- Rule sets are synthetic: destination-prefix forwarding, 5-tuple-style ACLs on common ports, in-port steering, and a table-miss rule. The generator seed is fixed (`20261122`), so runs are reproducible.
- Harmful widening is decided by sampling 256 packets inside the widened entry; a widening counted as harmless may still be harmful for a packet that was not sampled.
- Sampling (E5) draws entries with replacement.

## Run locally (Linux, ARM64 or x86-64)

```sh
sudo apt-get install -y build-essential libssl-dev
mkdir -p results
gcc -O2 -march=native -Wall -o tzbench src/tzbench.c -lcrypto
./tzbench 30
```
