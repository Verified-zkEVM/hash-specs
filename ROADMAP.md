# Roadmap: `hash-specs`

*A canonical library of formal, executable hash-function specifications in Lean 4. Each spec is documented to paper quality and checked by differential testing against real-world implementations. It is built to be compatible with the [Verified-zkEVM](https://github.com/Verified-zkEVM) ecosystem (CompPoly, ArkLib, …), so that projects there can adopt it when the time is right. The first priority is for these to become the canonical hash specs across Verified-zkEVM. A secondary aim is that the core could, in principle, be upstreamed to [CSLib](https://github.com/leanprover/cslib).*

Status: drafted 2026-10-11 as a plan; Phases 0–4 implemented by 2026-10-12. Phase 5 is optional, deferred work. Toolchain `v4.34.0`, matching CompPoly (§2.1). See [`LIT-REVIEW.md`](LIT-REVIEW.md) for prior work.

---

## 0. Goals and non-goals

**Goals:**
1. **Faithful specs.** Each hash has a *reference* spec that transcribes its standard or paper line by line, with section-level citations.
2. **Executable specs.** Each hash has a *fast* spec that runs on realistic inputs, plus a machine-checked proof that `fast = reference`.
3. **Earned confidence.** The fast spec is checked against official known-answer tests (KATs) and fuzzed against at least two independent implementations in the wild.
4. **Paper-quality documentation.** A Markdown README per hash family, with original diagrams of state, rounds and modes, an assurance table, and full citations. (Originally a Verso book; see decision 9 in §7.)
5. **Ecosystem-compatible.** Same toolchain, conventions and field library (CompPoly) as Verified-zkEVM, so any project there can depend on these specs without friction. Migrating existing org specs is **deferred** (see §6).
6. **CSLib-upstreamable in principle (secondary to goal 5).** The core spec library depends only on Mathlib and follows CSLib's conventions and layout, so it could later be contributed to CSLib's `Crypto` area with mostly mechanical changes. Nothing is upstreamed in v1 (see §6.2). Where CSLib compatibility conflicts with serving Verified-zkEVM, Verified-zkEVM wins.

**Non-goals for v1:**
- Cryptographic *security* proofs (indifferentiability, PRF, collision resistance). These belong in VCVio and ArkLib, and our specs are their inputs.
- Constant-time or side-channel properties.
- Verified *production* implementations, which is the job of Aeneas/hax/Charon work. A later phase may connect to them.
- MAC and KDF constructions on top of hashes (HMAC, KMAC, HKDF). These are cheap follow-ons.

**Scope decisions already made:**
- All four families are in scope: SHA-2, SHA-3/Keccak, BLAKE2/BLAKE3, and ZK-friendly hashes.
- The repo aims to be adoptable as a canonical upstream, but v1 does **not** include migrating or bridging existing org specs. When migration happens, each project decides how to do it (and can build its own bridge, with our help if wanted).
- The repo is designed for two futures, **in priority order**: (1) canonical specs for Verified-zkEVM repos; (2) upstreaming of the core to CSLib. CSLib-friendly choices are adopted when they cost Verified-zkEVM nothing, and dropped or postponed when they would get in its way (toolchain, dependencies, API shape, schedule). For now, all work happens in this repo.
- Proofs use two layers plus an equivalence theorem.
- Documentation is written in Markdown, one README per hash family (decision 9 in §7).

---

## 1. Landscape: what already exists in the org

Measured on 2026-10-11 from each repo's `HEAD`. It is context for later adoption, not v1 work. It also tells us which representations (for example `Nat` lanes versus `UInt64`) downstream users expect, which informs API design.

| Hash | Existing Lean spec(s) in Verified-zkEVM | Notes |
|---|---|---|
| Keccak-f[1600] / Keccak-256 / SHA-3 | `clean/Clean/Specs/Keccak256.lean` (over `Nat`); `zkLean/examples/zkLeanExamples/Sha3/Spec.lean`; `VCVio/HashSig/SLHDSA/Concrete/Keccak.lean` (pure Lean: SHAKE, SHA-3, Keccak-256); `evm-asm/EvmAsm/Codegen/Proofs/HashBridgeKeccakSpec.lean` | **At least 4 independent copies.** `VCVio/Extern/Hashing.lean` also wraps the C SHA-3 from mlkem-native through FFI. |
| SHA-256 | `clean/Clean/Specs/SHA256.lean`; `VCVio/HashSig/SLHDSA/Concrete/Sha2.lean` | |
| BLAKE2s / BLAKE2b-F | `leanerVM/LeanerVM/Semantics/Blake2s.lean` (well cited, RFC 7693); `evm-asm/.../Blake2f.lean` (EIP-152) | |
| BLAKE3 | `clean/Clean/Specs/BLAKE3.lean` | |
| RIPEMD-160 | `evm-asm/.../Ripemd160.lean` | EVM precompile |
| Poseidon | `clean/Clean/Specs/Poseidon{,Optimized,Constants}.lean` (circomlib, BN254) | The textbook and optimized versions are not proved equal. |
| Poseidon2 | `ArkLib/ArkLib/Data/Hash/Poseidon2.lean` (KoalaBear, translated from leanSpec) | |

External Lean specs to cite, and possibly bridge to later:
- SymCrypt/Aeneas FIPS 202 and FIPS 180-4 (arXiv 2609.15648)
- Nethermind `LeanCrypto` Keccak-256
- Axiom `openvm-fv` Keccak and SHA-256

**Infrastructure we build on:**

| Component | Pin / fact |
|---|---|
| Lean | We use **`v4.34.0`**, matching CompPoly, so that CompPoly's prebuilt release oleans and the Mathlib cache both work. (Latest stable is `v4.34.1`; `v4.35.0` is at rc4.) |
| CompPoly | Latest tag `v4.34.0-patch2` (no `v4.34.1` tag yet), `fixedToolchain := true`. Fields include BN254, BLS12-381/377, BabyBear (+Ext4), KoalaBear, Goldilocks, Mersenne31, Pasta, Secp256k1. Each field has `Basic` and `Fast` representations. |
| ArkLib | Lean `v4.34.0` |
| Lean module system | The org uses `module` / `public section` / `@[expose]` throughout. |
| CSLib | `leanprover/cslib`, Apache-2.0. Toolchain `v4.35.0-rc4` (it tracks Lean closely), Mathlib pinned to a commit, **no other direct dependencies**; adding dependencies is "managed carefully" (`DECISION_MAKING.md`). Has a `Cslib/Crypto/` area (`Primitives/PRG`, `Protocols/…`) whose README plans "a comprehensive library of primitives … together with their proofs of correctness". Conventions: every file imports `Cslib.Init`; module system; Mathlib style plus `CODESTYLE.md` (term-mode `def`s, readable proofs, no non-terminal `simp`, curated `grind` sets as API); `lake build --wfail`; `lake shake`; `mk_all`; root `references.bib`; PR titles `feat(...)`; AI-tool use must be disclosed in PRs; major developments discussed on Zulip first. |

---

## 2. Architecture

### 2.1 Toolchain and packaging
- **Toolchain:** `leanprover/lean4:v4.34.0`, matching CompPoly's `v4.34.0-patch2` tag (which sets `fixedToolchain := true`), with Mathlib `v4.34.0`. With matching toolchains, CompPoly's prebuilt release oleans are fetched instead of built (about 7 seconds instead of an hour), and Mathlib comes from `lake exe cache get`.
  - We first tried `v4.34.1`. It works, but CompPoly then has to be built from source, because oleans only load under the exact Lean version that built them. We moved to `v4.34.0` to keep fresh clones and CI fast.
  - Thereafter, move in lockstep with CompPoly's toolchain bumps, and tag our releases per toolchain (`v4.34.0`, `v4.34.0-patch1`, …), as CompPoly does.
- **Three layers, as separate Lake libraries in one package.** This is how one repo serves both Verified-zkEVM and a possible CSLib upstream:

  | Layer | Lake library | May depend on | Contents | Possible destination |
  |---|---|---|---|---|
  | 1. Core specs | `Hash`, `HashTests` | **Mathlib only** (plus what Mathlib brings: Batteries, Plausible, Aesop) | Reference and fast specs written in pure Lean, `Equiv` proofs, spec properties, `grind` sets, generic field specs over Mathlib's `[Field F]` with `ZMod p` instances | CSLib `Crypto`; canonical specs for Verified-zkEVM |
  | 2. ZK integration | `HashZK` | Layer 1 + CompPoly (and possibly Hex later) | Fast field instances on CompPoly `Fast` types, ring isomorphisms to `ZMod p`, CompPoly-typed API | Stays here; serves Verified-zkEVM |
  | 3. Tooling | `HashFFI`, `HashKAT`, `harness/`, `docs/` | anything | `@[export]` C entry points, full official KAT runs, Rust fuzzing, diagrams and research notes | Stays here permanently |

  - Layer 1 must never import layers 2 or 3. CI enforces this with an import check.
  - Downstream Verified-zkEVM repos can use Layer 1 alone, or Layer 2 if they want CompPoly types.
  - *Done 2026-10-27:* Lake declares dependencies per package, so anyone depending on a single package also fetched CompPoly. The layers are now two Lake packages in the same repo: the core `hash-specs` (Layer 1, Mathlib only) at the root, and `hash-specs-zk` in `zk/` (Layers 2 and 3's Lean libraries), which requires the core by path and CompPoly, and shares the core's `.lake/packages`. Downstream projects that need only Layer 1 require `hash-specs` and never fetch CompPoly.
- **Mathlib-free split, kept possible (decision 3 in §7).** Mathlib may be imported in Layer 1 for now. Files that don't need it (most byte-hash material) import only core and Batteries, and `lake shake` keeps imports minimal, so a Mathlib-free sub-library could be split off later without rewriting.
- **Dependencies:** Mathlib (Layer 1); CompPoly (Layer 2).
- **Conventions (a superset of CSLib's and the org's):**
  - Module system in every file (`module`, `public section`, `@[expose]`).
  - A `Hash/Init.lean` that mirrors `Cslib.Init` (linter options and default tactics), imported by every Layer 1 file. On upstreaming it is replaced by `Cslib.Init`.
  - The same `lakefile` linter options as CSLib (`weak.linter.mathlibStandardSet`, `weak.linter.flexible`, …) plus `autoImplicit = false`.
  - Mathlib style and CSLib `CODESTYLE.md`: term-mode `def`s, readable proofs, `simp only` rather than non-terminal `simp`, and curated `grind` sets treated as API.
  - `lake build --wfail`, `lake shake`, `mk_all`, `lake lint`.
  - Apache-2.0 with CSLib/Mathlib-style copyright headers that name the authors.
  - Record AI-tool use as we go (which tools, for what), so future CSLib PR descriptions can disclose it as their policy requires.

### 2.2 Proposed layout

This replaced the original placeholder stubs.

**Namespace mapping for CSLib.** The Layer 1 root `Hash` corresponds one-to-one to `Cslib.Crypto.Primitives.Hash`. For example, `Hash.Keccak.SHA3` would become `Cslib.Crypto.Primitives.Hash.Keccak.SHA3`. Upstreaming would then be a prefix rename plus swapping `Hash.Init` for `Cslib.Init`. General-purpose lemmas (bytes, `BitVec`, endianness) are kept in `Prelude/` so they can go wherever CSLib reviewers prefer, such as `Cslib/Foundations/Data`, or even Batteries or Mathlib.

```
hash-specs/
├── lakefile.toml, lean-toolchain
├── Hash.lean                    # Layer 1 root import (generated by mk_all)
├── Hash/                        # Layer 1 ↔ Cslib.Crypto.Primitives.Hash
│   ├── Init.lean                     # mirrors Cslib.Init
│   ├── Prelude/                      # bits, bytes, endianness, words, BitVec/UInt lemmas
│   ├── Construction/                 # modes, specified once and reused
│   │   ├── MerkleDamgard.lean        #   SHA-2, RIPEMD-160
│   │   ├── Sponge.lean               #   bit/byte sponge (FIPS 202 §4), pad10*1
│   │   ├── FieldSponge.lean          #   sponge over 𝔽 (Poseidon, Rescue, …)
│   │   └── HAIFA.lean / Tree.lean    #   BLAKE2 counters/flags, BLAKE3 tree
│   ├── SHA2/      { Params, Constants, Reference, Fast, Equiv, Instances }
│   ├── Keccak/    { KeccakP (all b, nr), SHA3, SHAKE, Keccak256, Fast, Equiv }
│   ├── BLAKE2/    { Reference, Fast, Equiv, Blake2bF (EIP-152) }
│   ├── BLAKE3/    { Compress, Chunk, Tree, Modes (hash/keyed/derive_key/XOF), Fast, Equiv }
│   ├── RIPEMD160/ (small; EVM precompile; decision 4 in §7)
│   ├── ZK/
│   │   ├── Common/   { SPN, MDS (Cauchy), GrainLFSR, RoundNumbers, Sbox }   # over [Field F]
│   │   ├── Poseidon/ { Reference, Optimized, Equiv, Instances/{Circom/BN254, …} }  # ZMod p
│   │   ├── Poseidon2/{ Reference, Instances/{HorizenLabs/BN254, Plonky3/{BabyBear,KoalaBear}, LeanSpec/KoalaBear} }
│   │   ├── RescuePrime/ { Reference, Instances/{RPO (Miden, Goldilocks)} }   # Phase 5, optional
│   │   ├── MiMC/     { MiMC-n/n, Feistel, MiMCSponge (circomlib) }           # Phase 5, optional
│   │   └── Pedersen/ (blocked on curves; optional, see §5 Phase 5)
├── HashTests/                    # Layer 1 tests: small decide-based KAT subset, Plausible
│                                      #   properties (CSLib-style, upstreamable)
├── zk/                                # package `hash-specs-zk` (Layers 2 and 3), requires the root by path
│   ├── HashZK/                        # Layer 2: CompPoly fast fields, ring isos to ZMod p
│   ├── HashFFI/Export.lean            # Layer 3: @[export] C-ABI entry points for the harness
│   └── HashKAT/                       # Layer 3: full official KAT runner (compiled executable)
│       └── vectors/                   # vendored vectors, with provenance + licence README
├── harness/                           # Rust cargo workspace, see §4
├── docs/                              # diagrams and research notes, see §3
│   └── diagrams/ (TikZ sources and SVGs), research/
└── references.bib                     # repo root, CSLib-compatible keys
```

### 2.3 The two-layer spec discipline

**Reference layer.** Written for a human auditor to compare against the PDF of the standard.
- Uses the standard's own names, indexing and data model. For example, FIPS 202 states are `Fin 5 → Fin 5 → Fin w → Bool`, and θ, ρ, π, χ, ι are named exactly as in §3.2.
- Every `def` docstring cites the standard section, such as `FIPS 202 §3.2.1, Algorithm 1`.
- Parameterised where the standard is:
  - Keccak-p[b, n_r] for every b ∈ {25, …, 1600}
  - SHA-2 by word size and its rotation/shift tables
  - Poseidon by (𝔽, t, α, R_F, R_P, constants, MDS)
- It need not be fast. It is executed on small inputs and test vectors only.

**Fast layer.** Built for executing and fuzzing.
- `UInt32`/`UInt64` lanes, `Vector` and `ByteArray`, in pure Lean (Layer 1). Fast field representations come from CompPoly `Fast` types in Layer 2.
- Must handle multi-megabyte inputs in reasonable time.

**Equivalence.** `theorem Fast.hash_eq_reference : Fast.hash = Reference.hash` for every instance or parameter set.
- **Proof strategy:** per-step lemmas (round function, message schedule, padding), then induction over rounds and blocks.
- **Tools:** `bv_decide` for bit-level steps; Mathlib's `Matrix`, `ZMod` and `ring`/`linear_combination` for field steps; CompPoly's ring isomorphisms in Layer 2.
- **Policy:** no `native_decide`, `sorry` or custom `axiom` anywhere in Layer 1, including its tests (use `decide +kernel`), matching Mathlib and CSLib practice. `native_decide` is allowed only in Layer 3 tooling. Enforced in CI with `#print axioms` checks.

**Constants are theorems, not trust.** Nothing-up-my-sleeve constants are computed from their definitions, and the tables are proved equal to the computed values:
- SHA-2 `K` and `H₀` from fractional parts of prime roots
- Keccak round constants from the `rc(t)` LFSR, and ρ offsets from the formula
- BLAKE2 IV from SHA-2
- Poseidon and Poseidon2 round constants from the Grain LFSR
- Cauchy MDS matrices

**Instance naming is explicit.** "Poseidon" alone is ambiguous.
- Names look like `Poseidon.Circom.BN254.t3` or `Poseidon2.Plonky3.KoalaBear.w16`.
- Each instance records the provenance of its parameters: paper table, reference repo and commit, and generation script.

**Spec-only properties.** Proved where they are cheap and useful to downstream users:
- Keccak-p is a bijection.
- Padding is injective.
- Output length is correct.
- XOF prefix consistency: `SHAKE(m, d₁)` is a prefix of `SHAKE(m, d₂)` when d₁ ≤ d₂.
- The incremental (streaming) API equals the one-shot API.

The last property caught a real bug in SymCrypt, so it gets a fast-layer streaming API and a proof.
*As implemented:* streaming equals one-shot is proved for SHA-2, SHA-3/SHAKE/Keccak-256, BLAKE2 and BLAKE3, for every way of splitting the message (`StreamLemmas.lean` in each directory).

---

## 3. Documentation

*Changed 2026-10-27 (decision 9 in §7):* the Verso book was dropped. Each family's `README.md` (in its `Hash/` directory) is now the documentation, and carries the notation, specification, security notes, assurance table, file and theorem index, and references. The diagrams moved to `docs/diagrams/` beside their TikZ sources and are embedded in the READMEs. The chapter structure below is kept as the plan the READMEs were written to; the worked examples and the HTML/PDF site are not carried over.

**Format:**
- Verso `Manual` genre, published as an HTML site via GitHub Pages, with a PDF via Verso's TeX backend if it is mature enough. Phase 0 checks this.
- Code blocks in the book are type-checked against the library, so the docs cannot drift.
- doc-gen4 API docs are generated alongside and cross-linked.

**Each hash chapter has a fixed structure:**
1. **Overview and history.** Designers, standardisation, where the hash is used (Ethereum, zkVMs, …), and which variants exist.
2. **Notation and data model.** Bit/byte ordering and endianness, explained with diagrams. This is the most common source of spec bugs.
3. **State and primitives.** Diagrams of the state layout, such as the Keccak 5×5×w cube with its planes, slices, rows, columns and lanes.
4. **The round function.** One diagram per step mapping (θ, ρ, π, χ, ι; Σ₀/Σ₁/Ch/Maj; G-function quarter-rounds; full and partial S-box layers), shown next to the reference Lean code.
5. **Mode of operation.** Diagrams of the Merkle–Damgård chain, the sponge's absorb and squeeze phases, BLAKE3's chunk and tree structure, and the field-sponge rate and capacity.
6. **Parameters and constants.** Where each constant comes from, and the Lean theorem proving the table correct.
7. **Worked example.** A small input traced through every step, with values generated by the Lean spec and checked in CI.
8. **Assurance status.** A table, generated from CI output, listing: KATs passed (count and source), fuzz executions and CPU-hours per oracle, the equivalence theorem and its axiom report, other known Lean specs of the same function (informational), and known deviations.
9. **Security notes.** Brief, fully cited pointers to the cryptanalysis and proof literature, such as the CCS 2019 indifferentiability result. No new claims.
10. **References.**

**Diagrams:**
- Original artwork only. Never copy figures from papers or standards. FIPS documents are US-government works, but paper figures are copyrighted, so everything is redrawn.
- Authored as TikZ, or hand-written SVG, in `docs/diagrams/`, and compiled to SVG in CI so the sources stay reviewable.
- Shared style: colour-blind-safe palette, readable in light and dark mode, consistent glyphs for XOR, addition modulo 2ʷ and rotation.
- Stretch goal: interactive round explorers. A Verso page embeds a JS widget driven by worked-example data exported from Lean.

**Citations:**
- One `references.bib` at the repo root, with keys chosen to merge cleanly into CSLib's root `references.bib`. Primary sources first: NIST FIPS 180-4 and 202, RFC 7693, the BLAKE3 spec, the Poseidon and Poseidon2 papers (USENIX Sec 2021; AFRICACRYPT 2023), the Rescue-Prime ePrint, the MiMC paper (ASIACRYPT 2016), and the EIP-152 text.
- Each entry includes a DOI or a stable URL and an access date.
- Reference-layer docstrings cite by section number and must stand on their own, because the READMEs would not go to CSLib.

---

## 4. Differential testing harness

### 4.1 Confidence pipeline, per hash

```
official KATs ──► Lean (fast) ◄──► Rust oracles ×≥2  (coverage-guided fuzzing)
                     ▲  proved equal
                Lean (reference) ◄── small-input property tests (Plausible)
```

1. **KATs** run in CI on every PR, from vendored official vectors with a provenance README (source URL, licence, and SHA-256 of each file). The full sets run as a compiled executable (`HashKAT`, Layer 3). A small representative subset is checked with `decide +kernel` in `HashTests` (Layer 1), which keeps that part upstreamable. Sources:
   - NIST CAVP/ACVP for SHA-2, SHA-3 and SHAKE, including the Monte Carlo tests
   - the BLAKE2 reference KATs and the BLAKE3 `test_vectors.json`
   - EIP-152 vectors
   - reference vectors from the Poseidon, Poseidon2 and Rescue authors and from leanSpec
2. **Reference vs fast in Lean** with Plausible. This is useful before the `Equiv` proof exists, and redundant (but cheap) afterwards.
3. **Lean fast vs Rust oracles**, in two modes:
   - **In-process (primary):** `HashFFI/Export.lean` exposes `@[export hs_<hash>]` C-ABI functions taking bytes, field-element limbs and parameters. Lake builds a static library. A `hashspecs-sys` Rust crate links it with the Lean runtime, initialises the runtime and the module once (with per-thread initialisation for fuzz workers), and offers safe wrappers. Fuzz targets use `cargo-fuzz` (libFuzzer), and `proptest` drives deterministic CI runs.
   - **Subprocess (fallback, and for the reference layer):** a Lean executable speaks a batched stdin/stdout protocol. It's slower, but portable and a useful first step.
   - **Stretch:** compile Lean's emitted C with `-fsanitize=fuzzer-no-link` so libFuzzer's coverage feedback also sees the Lean code paths.

### 4.2 Oracles

Each hash gets at least two oracles, chosen for independent code lineage. Many Keccak implementations derive from XKCP and correlated oracles hide bugs, so the lineage of each is recorded.

| Hash | Primary oracle | Independent second oracle | Other |
|---|---|---|---|
| SHA-224/256/384/512(/t) | RustCrypto `sha2` | `aws-lc-rs` (parts formally verified) | OpenSSL CLI |
| SHA-3, SHAKE | RustCrypto `sha3` | `tiny-keccak` | XKCP |
| Keccak-256 (Ethereum) | `tiny-keccak` | `alloy-primitives::keccak256` | go-ethereum (subprocess) |
| BLAKE2b/2s (+ keyed, param block) | RustCrypto `blake2` | `blake2b_simd` / libsodium | |
| BLAKE2b-F (EIP-152) | `revm` precompile | go-ethereum | |
| BLAKE3 (hash, keyed, derive_key, XOF) | official `blake3` crate | the BLAKE3 reference implementation (separate code) | |
| RIPEMD-160 | RustCrypto `ripemd` | OpenSSL | |
| Poseidon (circomlib BN254) | `light-poseidon` | `circomlibjs` (Node subprocess) | |
| Poseidon2 | Plonky3 `p3-poseidon2` (BabyBear/KoalaBear) | HorizenLabs `zkhash` (BN254 etc.) | leanSpec (Python subprocess) |
| Rescue-Prime / RPO | `miden-crypto` | the authors' reference implementation (Sage/Python) | |
| MiMC (circomlib) | `circomlibjs` | a gnark implementation (Go subprocess) | |
| Pedersen | `starknet-crypto` (StarkNet) / `circomlibjs` (BabyJubJub) | Zcash `sapling-crypto` (Jubjub) | |

### 4.3 Fuzzing strategy

**Structured inputs with `arbitrary`**, aimed at the edges where bugs live:
- **Length boundaries:**
  - SHA-256: 55, 56 and 64 bytes
  - SHA-512: 111, 112 and 128 bytes
  - Keccak-256: rate edges at 135 and 136 bytes
  - BLAKE2b: 128-byte blocks, with the final-block flag on an exact multiple
  - BLAKE3: 64-byte blocks, 1024-byte chunks, and powers of two of chunks for tree shape
- **Streaming:** random split points in incremental APIs, compared against one-shot calls.
- **XOF:** output lengths, including 0 and non-multiples of the rate.
- **Parameters:** BLAKE2 key, salt, personalisation and digest length; BLAKE3 context strings.
- **Field elements:** 0, 1, p−1, values ≥ p (to check that non-canonical inputs are rejected or reduced consistently), and random elements.

**CI tiers:**
- Every PR: KATs plus about 60 s of fuzz smoke per target.
- Nightly: hours of fuzzing on long-running runners, with corpora committed and minimised.
- Crashes and divergences become regression KATs automatically.

**Divergence triage.** A mismatch is *a bug somewhere*. Each mismatch gets an issue recording which side was wrong, judged against the standard text, and why. Bugs found in oracles are reported upstream responsibly.


### 4.4 Benchmarks (a record, not a requirement)

The harness also benchmarks each fast Lean specification against the implementations it is
differentially tested against (`criterion`, in-process through the same C exports). The results go
to `harness/BENCHMARKS.md` (`harness/scripts/bench_report.py`). This is only a record of relative
efficiency: there are no thresholds, and nothing fails if the Lean code is slower.
---

## 5. Phased roadmap

Sizes are relative (S/M/L/XL), not calendar estimates. Each phase ends with explicit exit criteria. **Phase 1 is a deliberately complete vertical slice:** every later hash reuses its pipeline.

### Phase 0: Foundations (M)
- Toolchain `v4.34.0` with Mathlib `v4.34.0`, CompPoly `v4.34.0-patch2` (prebuilt oleans) and Verso `v4.34.0` (§2.1).
- Set up the three-library Lake structure from §2.1, with a CI check that Layer 1 imports nothing outside Mathlib.
- `Hash/Init.lean` mirroring `Cslib.Init`, CSLib's linter options, `mk_all`, `lake shake` and `lake lint` in CI. Record a zero-warning baseline and enforce it (`--wfail`).
- A **CSLib-compatibility CI job** that builds Layer 1 against CSLib's current toolchain and Mathlib pin. It is non-blocking at first, and is there to surface drift early, not to force us onto release candidates.
- Write `CONTRIBUTING.md` with the spec style guide: naming, citation format, reference and fast layers, the axiom policy, instance naming, the CSLib code style rules, and the AI-use log.
- `Prelude`: byte, word and endianness utilities and their core `BitVec`/`UInt` lemmas.
- Harness skeleton: a `hashspecs-sys` crate links a trivial `@[export]` function and runs one `cargo-fuzz` target in CI on Linux and macOS.
- Verso skeleton: one chapter containing a compiled TikZ→SVG diagram, a type-checked code block and a bibliography citation, deployed to GitHub Pages.
- *As implemented:* doc-gen4 and checkdecls are deferred. The Verso book and module docstrings cover documentation for now, and doc-gen4 would add a second set of documentation dependencies. Verso's bibliography has no type for standards (FIPS, RFCs, EIPs), so the book cites those by name, section and link, and `references.bib` lists every source.
- **Exit:** CI is green end to end on the placeholder, and CompPoly builds on the chosen toolchain.

### Phase 1: SHA-256 vertical slice, then the rest of SHA-2 (L)
- `Construction/MerkleDamgard`, SHA-2 reference (FIPS 180-4 §§4–6), fast layer, `Equiv`, and derivation of the constants (`K`, `H₀`).
- CAVP SHAVS short, long and Monte Carlo KATs. Fuzzing against `sha2` and `aws-lc-rs`, plus streaming-vs-one-shot.
- A Verso chapter with all the elements of §3.
- Then extend to SHA-224, SHA-384, SHA-512 and SHA-512/224 and /256, which should be mostly parameter work.
- **Exit:** all SHA-2 variants pass KATs, reach a set fuzz budget (for example 10⁹ executions per oracle) with no divergence, have axiom-clean `Equiv` theorems, and have a complete chapter.

### Phase 2: SHA-3 / Keccak (L)
- Keccak-p[b, n_r] reference for every b, `Construction/Sponge` with pad10*1, SHA3-224/256/384/512, SHAKE128/256, and Ethereum Keccak-256 with `0x01` padding.
- Proofs: fast-layer `Equiv` for b = 1600, Keccak-p bijectivity, and XOF prefix consistency.
- CAVP SHA3VS KATs, fuzzing against `sha3`, `tiny-keccak` and `alloy`.
- **Exit:** the same criteria as Phase 1.

### Phase 3: BLAKE2 and BLAKE3 (L)
- BLAKE2b and BLAKE2s (RFC 7693, plus the parameter block for key, salt and personalisation), and the BLAKE2b-F compression function with a configurable round count (EIP-152).
- BLAKE3: the compression function, chunk chaining, the binary tree (`Construction/Tree`), the keyed, derive_key and XOF modes, and a proof that streaming equals one-shot.
- *As implemented:* each hash has `Reference`, `Fast`, `Stream` and `Equiv` files rather than the per-step files sketched in §2.2, and BLAKE2's counter and flag handling stays in `BLAKE2/Reference` instead of a separate `HAIFA` construction. BLAKE3 reuses the BLAKE2s round. `Construction/Tree` is generic over leaves, nodes and chaining values, and `Hash.Tree.finish_pushAll` proves that the chaining-value stack of BLAKE3 §5.1.2 computes the tree; the byte-level streaming theorem builds on it. BLAKE2 streaming is tested, not proved. The BLAKE2 equivalence covers keys of at most one block (RFC 7693 allows at most half a block). The second BLAKE3 oracle is the BLAKE3 team's reference implementation, vendored in `harness/blake3-reference`, since the other BLAKE3 crates found on crates.io are forks or wrappers of the official one. EIP-152 vector 8 (2³² − 1 rounds) is skipped in `hash-kat` as too slow.
- **Exit:** the same criteria as Phase 1.

### Phase 4: ZK-friendly hashes I, Poseidon and Poseidon2 (XL)
- **`ZK/Common`:**
  - a generic SPN permutation over Mathlib's `[Field F]` (Layer 1), with fast instances on CompPoly `Fast` types in `HashZK` (Layer 2)
  - power S-boxes x^α with a gcd(α, p−1) = 1 side condition
  - Grain-LFSR constant generation
  - Cauchy MDS generation, plus an MDS check for small t
  - round-number formulas as functions, with a table of the chosen instances
- **Poseidon** (Grassi et al., USENIX Sec 2021): the reference layer as in the paper, and the *optimized* form with sparse matrices and partial-round constant folding as used by circomlib, with `Equiv` between them. This closes the gap the Clean team noted.
  - Instances: circomlib BN254 for t = 2..17 (or the subset in use).
- **Poseidon2** (Grassi, Khovratovich, Schofnegger, AFRICACRYPT 2023): external and internal matrices.
  - Instances: HorizenLabs BN254 t = 3, Plonky3 BabyBear and KoalaBear widths 16 and 24, leanSpec KoalaBear.
- `Construction/FieldSponge`, including the domain separation conventions each ecosystem uses (circomlib's capacity initialisation versus Plonky3's padding-free sponge). Each convention is documented as its own instance.
- Use the circomlib and leanSpec instances already used by `clean` and `ArkLib` as test instances, so later adoption is easy.
- **Exit:** every listed instance passes its authors' vectors, is fuzzed against two oracles, and has axiom-clean `Equiv` theorems.
- *As implemented (closed 2026-10-12):*
  - **Instances.** Poseidon: circomlib BN254, widths 2–17. Poseidon2: HorizenLabs BN254 t = 3, and Plonky3 0.8.0 BabyBear and KoalaBear at widths 16 and 24.
  - **Field representations.** The executable code runs over a small class of field operations, `Hash.ZK.FieldOps`, rather than a generic SPN over `[Field F]`. It runs on three representations: `ZMod p` (Layer 1), CompPoly's Montgomery fields (`HashZK`), and raw limbs or natural numbers for the C exports (`HashZK.Raw`, Mathlib-free). Maps that preserve the operations carry the proofs between them.
  - **Constants.** Round constants and Cauchy matrices are defined as Grain output. The kernel cannot evaluate Grain at these sizes, so they are checked against the authors' vectors by computation, not proved equal to published tables.
  - **Field sponges.** `Construction/FieldSponge` covers Plonky3's padding-free sponge and truncated-permutation compression. circomlib's convention is its one-shot hash with a caller-set capacity element.
  - **Oracles.** Plonky3 is the only implementation of its 31-bit Poseidon2 instances (SP1's is a fork). Those instances are therefore checked against Plonky3's scalar and SIMD code paths rather than against two independent implementations.
  - **Not done.** leanSpec has dropped Poseidon2 (it now uses Poseidon1 over KoalaBear), and its last Poseidon2 used Plonky3's superseded KoalaBear constant order. Its instance is therefore not included; the current Plonky3 KoalaBear instance is the one ArkLib transcribes. ArkLib's transcription indexes the external round constants incorrectly, which is worth reporting upstream.
  - **Deferred (decided 2026-10-12).**
    - Poseidon's optimized form, as circomlib computes it, with its `Equiv` to the reference. circomlib computes it with constants moved back through `M⁻¹`, sparse partial-round matrices and the `P` matrix.
    - Round-number formulas as functions; the chosen numbers are a table.
    - An MDS check for small `t`.

### Phase 5: ZK-friendly hashes II (optional, deferred future work; not in v1)
*Decided 2026-10-12:* the v1 scope ends with Phase 4. This phase is optional and deferred: none of it is on the v1 critical path, and Phase 6 does not wait for it. It is kept here as the plan for whoever picks it up. The README, previously the last step of this phase, moves to Phase 6.
- **Rescue-Prime** (Szepieniec, Ashur, Dhooghe), including the inverse S-box x^{1/α}, and **RPO** (Miden, Goldilocks).
- **MiMC:** MiMC-n/n, the Feistel variant, and circomlib's `MiMCSponge` over BN254.
- **Pedersen hashes** need twisted-Edwards and short-Weierstrass curve arithmetic that CompPoly doesn't provide (ArkLib has BN254 G1 only). Per decision 6, specify the hash over an abstract group first, and add concrete instances (BabyJubJub, Jubjub, the Stark curve) once the curves exist, possibly co-developed in CompPoly, ArkLib or Mathlib.
- **Stretch candidates**, each needing a short survey of real-world use first: Anemoi, Griffin, Monolith, Tip5, Reinforced Concrete.
- **Exit:** per hash, the same criteria as Phase 4.

### Phase 6: Hardening and v1.0 (M)
- Write a nice, readable `README.md`: what the library is, which hashes it covers and how far each is assured, how to depend on it, links to the docs site, roadmap and literature review, and how to contribute.
- An external review of the reference layers against the standards. Ideally an independent reader per family, with sign-off recorded in each chapter's assurance table.
- Prebuilt release oleans in CompPoly's style (`preferReleaseBuild`), versioning and a changelog.
- Write or finish the per-repo upstreaming records described in §6, including one for CSLib. They can be started earlier, for example after each family is done.
- **Exit:** v1.0 tagged and the docs site published. The library is ready for others to adopt (§6).

**Rough dependency graph:**
```
P0 ──► P1 ──► P2 ──► P3
          └──► P4 ··► P5          P6 after P3 and P4
                                  P5: optional, deferred, outside v1
                                  §6 adoption: whenever ready, outside the v1 critical path
```
P2/P3 and P4 can run in parallel once Phase 1 has proved the pipeline.

---

## 6. Future: adoption and upstreaming (deferred, not in v1)

There are two possible destinations, in priority order: Verified-zkEVM first, CSLib second. Neither is v1 work, but the repo's structure keeps both open. If both are on the table at once, Verified-zkEVM adoption goes first, and CSLib upstreaming should not change APIs that Verified-zkEVM repos already depend on.

### 6.1 Adoption by Verified-zkEVM repos

Migration happens when the Verified-zkEVM colleagues judge it appropriate, and each project decides how. v1 only makes adoption *possible*: compatible toolchain, CompPoly fields, ergonomic representations and good docs. Notes for when the time comes:

- **Circular dependencies.** Once a project depends on `hash-specs`, a proof that imports that project cannot live in `hash-specs`. So bridge theorems belong in the downstream repo, or in a throwaway package that depends on both sides.
- **Typical bridge shape** (illustrative):
  ```
  theorem Clean.Specs.Keccak256.hash_eq (m) : Clean.Specs.Keccak256.hash m = Hash.Keccak.keccak256 m
  ```
  - Representation adapters (`Nat` lanes versus `UInt64`, `Vector` versus `ByteArray`) are stated and proved as lemmas. We can provide the common ones in `Hash`.
- **Bridges are evidence for both sides.** If a bridge can't be proved, someone has a bug, and the differential harness can show which side it is.
- **We can help** by pairing on bridges, adding conversion lemmas, or adding instances a project needs.
- **Upstreaming record (to do at some point, at the latest in Phase 6).** Keep a local record of everything each relevant repo (`clean`, `VCVio`, `zkLean`, `ArkLib`, `leanerVM`, `evm-asm`, …) would need in order to upstream, so that when a project is ready the work is already scoped. For example, one file per repo under `docs/upstreaming/<repo>.md`, listing:
  - which of its specs overlap ours (file paths, pinned to a commit) and which `Hash` definitions replace them
  - the representation differences, and the conversion lemmas needed to bridge them
  - the proposed bridge theorem statements
  - dependency and toolchain differences (Lean version, Mathlib/CompPoly pins, module system)
  - instances or parameters the project uses that we don't yet cover
  - any behavioural differences found by differential testing or attempted bridges
  - downstream call sites that would need to change
- **Optional:** bridges to external Lean specs (SymCrypt/Aeneas, Nethermind `LeanCrypto`, Axiom `openvm-fv`).

### 6.2 Upstreaming the core to CSLib (secondary)

Only Layer 1 (`Hash`, `HashTests`) is a candidate. CompPoly integration, FFI, the Rust harness, full KAT runs and the READMEs stay here.

- **What makes it mechanical:** the namespace mapping in §2.2, `Hash.Init` mirroring `Cslib.Init`, identical linters and style, Mathlib-only dependencies, a merge-ready `references.bib`, and the CSLib-compat CI job.
- **Remaining work at that point:**
  - port to CSLib's toolchain and Mathlib pin
  - rename the prefix and swap the `Init` import
  - decide with reviewers where the `Prelude` lemmas belong
  - possibly generalise or reuse abstractions CSLib reviewers ask for (for example a generic permutation or sponge interface, `BitVec n` / `Fin n → Bool` conventions as in `Cslib.Crypto.Primitives.PRG`, or later security notions built on `Cslib.Probability.PMF`)
- **Process, when the time comes:**
  1. Open a CSLib Zulip thread first (their guidelines ask this for major developments), possibly proposing a working group.
  2. Send small PRs in dependency order: `Prelude` utilities, then constructions (sponge, Merkle–Damgård), then one hash at a time (reference layer first, then fast layer and `Equiv`).
  3. Disclose AI-tool use in each PR, using the AI-use log.
- The upstreaming record (§6.1) gets a `docs/upstreaming/cslib.md` entry covering the same points: file mapping, toolchain gap, open design questions for reviewers.

---

## 7. Decisions

Settled on 2026-10-11. These are the defaults proposed earlier, accepted, with decision 3 as edited.

1. **Package and namespace name.** Keep `Hash`, matching the repo, with the root mapping to `Cslib.Crypto.Primitives.Hash` (§2.2). Revisit if the repo is transferred into the org.
2. **Repo home.** Develop here. Moving it into `Verified-zkEVM` is a decision for after talking with colleagues.
3. **Mathlib-free core split.** Organise the code in a way that a Mathlib-free core could be split off later, if we decide to. For now, feel free to import Mathlib.
4. **RIPEMD-160.** Include it, since it's small. It's an EVM precompile and `evm-asm` already has a copy.
5. **Poseidon and Poseidon2 instances.** The instances real targets use: circomlib, Plonky3, leanSpec, HorizenLabs. Adjust if verified-zkevm.org priorities point elsewhere.
6. **Pedersen curve strategy.** Abstract group first, concrete curves when available.
7. **PDF output.** HTML site first; PDF only if Verso's TeX backend is adequate. *Superseded by decision 9.*
8. **SP 800-185 (cSHAKE, KMAC, TupleHash, ParallelHash).** Deferred to after v1.
9. **Documentation format** (*decided 2026-10-27*). Drop the Verso book: it was a heavy dependency for every downstream user, and it duplicated the per-family READMEs. Each family's README is the documentation, with the book's assurance tables and diagrams folded in.

---

## 8. Risks and mitigations

| Risk | Mitigation |
|---|---|
| Linking the Lean runtime into Rust (static linking, initialisation, threads) is fiddly across platforms. | Prove it out in Phase 0 on a trivial export. The subprocess protocol is always available as a fallback. |
| Toolchain drift: CompPoly sets `fixedToolchain`, so we move only when it does. | Track CompPoly's tags and bump in lockstep. If a needed Lean fix lands before CompPoly bumps, CompPoly can be built from source on a newer toolchain, as tried with `v4.34.1` (§2.1). |
| `Equiv` proofs over many rounds or large states blow up `bv_decide` or elaboration. | Per-round lemmas plus induction. Avoid unfolding whole permutations. Never fall back to `native_decide` in the trust chain. |
| Correlated oracles, for example XKCP-derived Keccak implementations, hide the same bug. | Record the lineage of each oracle and require one independent implementation per hash. Official KATs act as a third source. |
| ZK hashes are underspecified: "Poseidon" names many incompatible variants. | Explicit instance naming, parameter provenance (repo and commit), and generating constants instead of pasting them. |
| Copyright of diagrams and of text quoted from papers. | Original diagrams only. Quote only short spans, with citations. |
| Licences of vendored test vectors and constants. Some sources are under copyleft licences: for example circomlib is LGPL-3.0 and circomlibjs is GPL-3.0, while Plonky3, HorizenLabs' Poseidon2 and `light-poseidon` are Apache-2.0 and leanSpec is MIT. | Record each vendored file's licence in the provenance README. Prefer generating constants (Grain LFSR) over copying them. Use copyleft tools only as external oracles run as subprocesses, never vendored into the Apache-2.0 tree. |
| Trusted computing base of the testing itself: the Lean compiler and runtime, and the C toolchain. | State it in the docs. The `Equiv` proofs are kernel-checked, and only the fast-layer execution relies on the compiler. |
| Two ecosystems pull the toolchain in different directions: Verified-zkEVM is on `v4.34.x` with CompPoly, while CSLib tracks release candidates and a Mathlib commit. | Main build follows Verified-zkEVM. A non-blocking CSLib-compat CI job builds Layer 1 on CSLib's pin. Layer 1 never depends on CompPoly. |
| CSLib reviewers may want more general abstractions, or may decline parts such as fast layers or large constant tables. | Keep the reference layers and properties self-contained so they can go first. Discuss the design on Zulip before upstreaming. Anything declined stays here. |
| Adoption friction later: downstream representations differ from ours. | Keep the API ergonomic for common representations (`Nat`/`UInt64` lanes, `Vector`/`ByteArray`, CompPoly fields), and provide documented conversion lemmas. |

---

## 9. Definition of done, per hash

A hash is **done** when:
- [ ] The reference spec cites a section of the standard on every definition.
- [ ] Constants are derived and the tables proved equal to the derived values.
- [ ] The fast spec has an `Equiv` theorem, and `#print axioms` shows only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- [ ] All official KATs pass in CI, from vendored vectors with recorded provenance.
- [ ] It is fuzzed against at least 2 independent oracles, past the fuzz budget, with no open divergences.
- [ ] Streaming-vs-one-shot (and XOF prefix consistency, where relevant) is proved or tested.
- [ ] It has a README covering the §3 sections, with original diagrams and an assurance table.
- [ ] The build has zero warnings.
- [ ] Its Layer 1 files pass CSLib's linters and style rules. (The CSLib-compat CI job is advisory: a failure there is tracked, but it doesn't block a hash from being done.)
