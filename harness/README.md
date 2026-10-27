# Differential-testing harness

This Cargo workspace links the fast Lean specifications into Rust in-process and compares them
with independent implementations (ROADMAP.md §4).

- `hash-lean/`: the bindings. `build.rs` runs `lake build HashFFI:static Hash:static
  HashZK:static` in the `zk` package (`zk/`) and builds CompPoly's zero-import Montgomery arithmetic (skip with
  `HASH_LEAN_SKIP_LAKE=1`), and links the Lean static libraries and runtime. A small C shim
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
| SHA3-224/256/384/512 | `Hash.sha3x*`, `Hash.sha3x*Init` (streaming) | RustCrypto `sha3`, `tiny-keccak`, AWS-LC (256/384/512) |
| SHAKE128, SHAKE256 | `Hash.shake128`, `Hash.shake256`, `Hash.shake*Init` (streaming) | RustCrypto `sha3`, `tiny-keccak` |
| Keccak-256 (Ethereum) | `Hash.keccak256`, `Hash.keccak256Init` (streaming) | RustCrypto `sha3`, `tiny-keccak`, `alloy-primitives` |
| BLAKE2b, BLAKE2s (key, salt, personalisation, any output length) | `Hash.blake2bWith`, `Hash.blake2sWith`, `Hash.blake2*Init` (streaming) | `blake2b_simd`/`blake2s_simd`, RustCrypto `blake2` (unkeyed any length; keyed with salt and personalisation at full length) |
| BLAKE2b `F` precompile (EIP-152) | `Hash.blake2bPrecompile` | `revm-precompile`, `eip-152` |
| BLAKE3 (`hash`, `keyed_hash`, `derive_key`, any output length) | `Hash.blake3Xof`, `Hash.blake3Keyed`, `Hash.blake3DeriveKey`, `Hash.blake3*Init` (streaming) | `blake3`, the BLAKE3 team's reference implementation (`blake3-reference/`, vendored) |
| Poseidon, circomlib's BN254 instances (1 to 16 inputs) | `HashZK.Raw.Poseidon.poseidonNat` (proved equal to `Hash.ZK.Poseidon.Circom.poseidon`) | `poseidon-rs` (all widths), `light-poseidon` (up to 12 inputs) |
| Poseidon2: Plonky3 BabyBear and KoalaBear, widths 16 and 24 | `HashZK.Raw.Poseidon2.*` (proved equal to `Hash.ZK.Poseidon2.Plonky3.permutation`) | Plonky3 0.8.0, scalar and SIMD (packed) code paths |
| Poseidon2: HorizenLabs BN254, width 3 | `HashZK.Raw.Poseidon2.hlBn254` (proved equal to `Hash.ZK.Poseidon2.hlBn254Permutation`) | `zkhash` (HorizenLabs' reference), Plonky3's `p3-bn254` with `zkhash`'s constants |

Lineage: RustCrypto `sha3` and `tiny-keccak` are independent Rust implementations; AWS-LC's SHA-3
descends from BoringSSL/OpenSSL. `alloy-primitives::keccak256` uses `tiny-keccak` by default, so
it is not independent of it; it is included because it is the function Ethereum tooling calls.
`blake2b_simd` and RustCrypto `blake2` are independent. `revm-precompile`'s `F` is vendored from
`blake2b_simd`, so it is included as the function Ethereum clients run rather than as an
independent check; the `eip-152` crate (Parity's OpenEthereum implementation, published from the
Tetsy Vapory fork) is independent of both. `eip-152` is GPL-3.0 and is only a dev-dependency of
the tests; it is not linked into anything distributed. The BLAKE3 reference implementation is
by the same team as the `blake3` crate but shares no code with it: it is a minimal portable
implementation, vendored unmodified in `blake3-reference/`. `poseidon-rs` (iden3) carries
circomlib's published constant tables, and `light-poseidon` (Light Protocol) constants generated
with the Poseidon reference script; the Lean specification derives its constants from the Grain
LFSR itself, so agreement also checks the constants. For Poseidon2, Plonky3 is the only
implementation of its BabyBear and KoalaBear instances (SP1's is a fork), so the tests compare
against two code paths of Plonky3 rather than two implementations; Plonky3's BN254 permutation
takes its constants from `zkhash`, so only its permutation code is independent of `zkhash`.

```sh
cd hash-lean && cargo test --release          # differential tests
cd fuzz && cargo +nightly fuzz run sha2       # fuzzing
cd hash-lean && cargo bench && python3 ../scripts/bench_report.py   # benchmark record
```
