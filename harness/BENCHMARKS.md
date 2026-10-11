# Benchmarks

Throughput of the Lean fast specifications next to the implementations they are
differentially tested against. **This is a record of relative efficiency, not a
requirement.** The Lean code is a specification: it is written to be proved equal to the
reference specification, not to compete with optimised libraries.

- Recorded: 2026-10-11
- Machine: Apple M3 Max, Darwin arm64
- Command: `cargo bench --bench throughput` in `harness/hash-lean`, then
  `python3 harness/scripts/bench_report.py`
- Lean is called in-process through the C exports in `HashFFI/Export.lean`, so the
  numbers include copying the message into a Lean `ByteArray`.
- "× Lean" is how many times faster than the Lean fast specification each
  implementation is.

## SHA-256

| Message | lean | aws-lc | rustcrypto |
|---|---|---|---|
| 64 B | 13.1 MiB/s | 1013.3 MiB/s (77.6× Lean) | 208.3 MiB/s (15.9× Lean) |
| 1 KiB | 33.5 MiB/s | 2.2 GiB/s (66.4× Lean) | 409.2 MiB/s (12.2× Lean) |
| 64 KiB | 36.2 MiB/s | 2.6 GiB/s (73.2× Lean) | 430.5 MiB/s (11.9× Lean) |
| 1 MiB | 36.2 MiB/s | 2.6 GiB/s (73.5× Lean) | 446.7 MiB/s (12.3× Lean) |

## SHA-512

| Message | lean | aws-lc | rustcrypto |
|---|---|---|---|
| 64 B | 7.6 MiB/s | 608.1 MiB/s (80.3× Lean) | 315.2 MiB/s (41.6× Lean) |
| 1 KiB | 27.7 MiB/s | 1.3 GiB/s (48.5× Lean) | 606.4 MiB/s (21.9× Lean) |
| 64 KiB | 36.0 MiB/s | 1.5 GiB/s (43.3× Lean) | 696.5 MiB/s (19.4× Lean) |
| 1 MiB | 36.1 MiB/s | 1.5 GiB/s (42.9× Lean) | 703.5 MiB/s (19.5× Lean) |
