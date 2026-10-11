# Differential-testing harness

This Cargo workspace links the fast Lean specifications into Rust in-process and compares them
with independent implementations (ROADMAP.md §4).

- `hash-lean/`: the bindings. `build.rs` runs `lake build HashFFI:static Hash:static` (skip
  with `HASH_LEAN_SKIP_LAKE=1`) and links the Lean static libraries and runtime. A small C shim
  (`csrc/shim.c`) wraps the `static inline` helpers of `lean.h`. Each hash is a safe function
  `fn(&[u8]) -> Vec<u8>`; streaming interfaces are exposed as functions that absorb a message
  in pieces of given sizes (for example `sha2_stream`).
  - `tests/`: differential tests: exhaustive short lengths around every padding boundary, large
    messages, `proptest` random messages, streaming in random pieces against the one-shot
    digest, and concurrent calls from several threads.
  - `benches/`: `criterion` throughput benchmarks. They are a record of relative efficiency,
    not a requirement; `scripts/bench_report.py` writes the results to `BENCHMARKS.md`.
- `fuzz/`: `cargo-fuzz` targets (libFuzzer). `corpus/` holds the committed seed corpora.
  Each hash has a one-shot target (for example `sha2`) and, where the Lean library has a
  streaming interface, a target with fuzzer-chosen piece sizes (for example `sha2_stream`).

| Hash | Lean | Oracles |
|---|---|---|
| SHA-224/256/384/512, SHA-512/224, SHA-512/256 | `Hash.sha*`, `Hash.sha*Init` (streaming) | RustCrypto `sha2`, AWS-LC (`aws-lc-rs`) |

```sh
cd hash-lean && cargo test --release          # differential tests
cd fuzz && cargo +nightly fuzz run sha2       # fuzzing
cd hash-lean && cargo bench && python3 ../scripts/bench_report.py   # benchmark record
```
