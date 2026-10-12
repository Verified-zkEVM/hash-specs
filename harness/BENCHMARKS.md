# Benchmarks

Throughput of the Lean fast specifications next to the implementations they are
differentially tested against. **This is a record of relative efficiency, not a
requirement.** The Lean code is a specification: it is written to be proved equal to the
reference specification, not to compete with optimised libraries.

- Recorded: 2026-10-12
- Machine: Apple M3 Max, Darwin arm64
- Command: `cargo bench --bench throughput` in `harness/hash-lean`, then
  `python3 harness/scripts/bench_report.py`
- Lean is called in-process through the C exports in `HashFFI/Export.lean`, so the
  numbers include copying the message into a Lean `ByteArray`.
- "× Lean" is how many times faster than the Lean fast specification each
  implementation is.

## BLAKE2b-512

| Message | lean | blake2b_simd | rustcrypto |
|---|---|---|---|
| 64 B | 5.8 MiB/s | 535.5 MiB/s (91.6× Lean) | 495.5 MiB/s (84.8× Lean) |
| 1 KiB | 13.8 MiB/s | 1.3 GiB/s (93.1× Lean) | 1.3 GiB/s (94.0× Lean) |
| 64 KiB | 14.1 MiB/s | 1.3 GiB/s (92.6× Lean) | 1.3 GiB/s (95.9× Lean) |
| 1 MiB | 14.1 MiB/s | 1.3 GiB/s (93.5× Lean) | 1.3 GiB/s (96.6× Lean) |

## BLAKE2s-256

| Message | lean | blake2s_simd | rustcrypto |
|---|---|---|---|
| 64 B | 12.5 MiB/s | 611.4 MiB/s (49.0× Lean) | 637.5 MiB/s (51.1× Lean) |
| 1 KiB | 15.5 MiB/s | 770.6 MiB/s (49.8× Lean) | 788.0 MiB/s (50.9× Lean) |
| 64 KiB | 15.8 MiB/s | 790.8 MiB/s (50.1× Lean) | 800.3 MiB/s (50.7× Lean) |
| 1 MiB | 15.6 MiB/s | 781.3 MiB/s (50.1× Lean) | 797.9 MiB/s (51.1× Lean) |

## BLAKE3

| Message | lean | blake3 | reference |
|---|---|---|---|
| 64 B | 13.8 MiB/s | 856.3 MiB/s (62.2× Lean) | 484.3 MiB/s (35.2× Lean) |
| 1 KiB | 15.1 MiB/s | 1.1 GiB/s (71.3× Lean) | 755.1 MiB/s (49.9× Lean) |
| 64 KiB | 14.2 MiB/s | 2.0 GiB/s (141.9× Lean) | 744.2 MiB/s (52.3× Lean) |
| 1 MiB | 14.2 MiB/s | 2.0 GiB/s (141.5× Lean) | 746.7 MiB/s (52.6× Lean) |

## Keccak-256

| Message | lean | rustcrypto | tiny-keccak |
|---|---|---|---|
| 64 B | 590.9 KiB/s | 338.7 MiB/s (586.9× Lean) | 320.5 MiB/s (555.3× Lean) |
| 1 KiB | 2.1 MiB/s | 787.2 MiB/s (381.4× Lean) | 716.0 MiB/s (346.9× Lean) |
| 64 KiB | 2.4 MiB/s | 857.8 MiB/s (351.3× Lean) | 774.5 MiB/s (317.2× Lean) |
| 1 MiB | 2.4 MiB/s | 858.5 MiB/s (355.7× Lean) | 777.5 MiB/s (322.1× Lean) |

## SHA-256

| Message | lean | aws-lc | rustcrypto |
|---|---|---|---|
| 64 B | 14.0 MiB/s | 1.0 GiB/s (73.7× Lean) | 224.9 MiB/s (16.0× Lean) |
| 1 KiB | 34.4 MiB/s | 2.5 GiB/s (75.9× Lean) | 443.7 MiB/s (12.9× Lean) |
| 64 KiB | 37.7 MiB/s | 2.8 GiB/s (75.4× Lean) | 472.7 MiB/s (12.6× Lean) |
| 1 MiB | 37.8 MiB/s | 2.8 GiB/s (76.9× Lean) | 471.5 MiB/s (12.5× Lean) |

## SHA-512

| Message | lean | aws-lc | rustcrypto |
|---|---|---|---|
| 64 B | 8.0 MiB/s | 653.0 MiB/s (81.8× Lean) | 328.2 MiB/s (41.1× Lean) |
| 1 KiB | 28.9 MiB/s | 1.4 GiB/s (50.7× Lean) | 635.8 MiB/s (22.0× Lean) |
| 64 KiB | 37.9 MiB/s | 1.6 GiB/s (44.5× Lean) | 734.0 MiB/s (19.4× Lean) |
| 1 MiB | 37.2 MiB/s | 1.6 GiB/s (45.0× Lean) | 728.2 MiB/s (19.6× Lean) |

## SHA3-256

| Message | lean | aws-lc | rustcrypto |
|---|---|---|---|
| 64 B | 596.1 KiB/s | 294.3 MiB/s (505.5× Lean) | 342.5 MiB/s (588.3× Lean) |
| 1 KiB | 2.1 MiB/s | 830.2 MiB/s (403.0× Lean) | 786.6 MiB/s (381.9× Lean) |
| 64 KiB | 2.4 MiB/s | 947.2 MiB/s (386.8× Lean) | 864.1 MiB/s (352.9× Lean) |
| 1 MiB | 2.4 MiB/s | 934.6 MiB/s (388.0× Lean) | 856.2 MiB/s (355.4× Lean) |
