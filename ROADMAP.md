# Roadmap: `hash-specs`

*A canonical library of formal, executable hash-function specifications in Lean 4. Each spec is documented to paper quality and checked by differential testing against real-world implementations. It is designed to be the shared upstream for the [Verified-zkEVM](https://github.com/Verified-zkEVM) organization.*

Status: **plan only**, drafted 2026-10-11. See [`LIT-REVIEW.md`](LIT-REVIEW.md) for prior work.

---

## 0. Goals and non-goals

**Goals:**
1. **Faithful specs.** Each hash has a *reference* spec that transcribes its standard or paper line by line, with section-level citations.
2. **Executable specs.** Each hash has a *fast* spec that runs on realistic inputs, plus a machine-checked proof that `fast = reference`.
3. **Earned confidence.** The fast spec is checked against official known-answer tests (KATs) and fuzzed against at least two independent implementations in the wild.
4. **Paper-quality documentation.** A Verso book with one chapter per hash, original diagrams of state, rounds and modes, and full citations.
5. **Org-wide canonical upstream.** Existing specs in `clean`, `VCVio`, `zkLean`, `ArkLib`, `leanerVM` and `evm-asm` are proved equal to ours ("bridges"), then migrated to depend on this library.

**Non-goals for v1:**
- Cryptographic *security* proofs (indifferentiability, PRF, collision resistance). These belong in VCVio and ArkLib, and our specs are their inputs.
- Constant-time or side-channel properties.
- Verified *production* implementations, which is the job of Aeneas/hax/Charon work. A later phase may connect to them.
- MAC and KDF constructions on top of hashes (HMAC, KMAC, HKDF). These are cheap follow-ons.

**Scope decisions already made:**
- All four families are in scope: SHA-2, SHA-3/Keccak, BLAKE2/BLAKE3, and ZK-friendly hashes.
- The repo will be the canonical upstream for the org.
- Proofs use two layers plus an equivalence theorem.
- Documentation is written in Verso.

---

## 1. Landscape: what already exists in the org

Measured on 2026-10-11 from each repo's `HEAD`. This list is what drives the bridge and migration work.

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
| CompPoly | `v4.34.0-patch2`, `fixedToolchain := true`. Fields include BN254, BLS12-381/377, BabyBear (+Ext4), KoalaBear, Goldilocks, Mersenne31, Pasta, Secp256k1. Each field has `Basic` and `Fast` representations. |
| ArkLib | Lean `v4.34.0` |
| Verso | Tag `v4.34.0` exists |
| Lean module system | The org uses `module` / `public section` / `@[expose]` throughout. |

---

## 2. Architecture

### 2.1 Toolchain and packaging
- **Toolchain:** pin `leanprover/lean4:v4.34.0`, down from the current `v4.34.1`, to match CompPoly and ArkLib. CompPoly's `fixedToolchain` means downstream repos must agree. Afterwards, bump in lockstep with CompPoly and tag releases the same way (`v4.34.0`, `v4.34.0-patch1`, …).
- **Dependencies:** `CompPoly` (which brings Mathlib), `verso` (docs only), `plausible` (property tests), and `doc-gen4` plus `checkdecls` (org convention).
- **Conventions:**
  - Module system in every file
  - `autoImplicit = false`
  - Mathlib linter set
  - Apache-2.0 headers, with file headers in the ArkLib/CompPoly style
- **Open packaging decision:** byte-oriented hashes don't need Mathlib, but consumers like `evm-asm` may want a light dependency. Phase 0 checks whether every intended consumer already depends on Mathlib.
  - If they all do, use one package.
  - If not, split into a Mathlib-free `hash-specs-core` (bytes, SHA, Keccak, BLAKE, RIPEMD) and `hash-specs` (field hashes, built on CompPoly) in a monorepo.

### 2.2 Proposed layout

This replaces the current `HashSpecs/{BLAKE,Poseidon,SHA}.lean` stubs.

```
hash-specs/
├── lakefile.toml, lean-toolchain
├── HashSpecs.lean                    # root import
├── HashSpecs/
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
│   ├── RIPEMD160/ (small; EVM precompile; optional, see §7)
│   ├── ZK/
│   │   ├── Common/   { SPN, MDS (Cauchy), GrainLFSR, RoundNumbers, Sbox }
│   │   ├── Poseidon/ { Reference, Optimized, Equiv, Instances/{Circom/BN254, …} }
│   │   ├── Poseidon2/{ Reference, Instances/{HorizenLabs/BN254, Plonky3/{BabyBear,KoalaBear}, LeanSpec/KoalaBear} }
│   │   ├── RescuePrime/ { Reference, Instances/{RPO (Miden, Goldilocks)} }
│   │   ├── MiMC/     { MiMC-n/n, Feistel, MiMCSponge (circomlib) }
│   │   └── Pedersen/ (blocked on curves, see §5 Phase 5)
│   └── FFI/Export.lean               # @[export] C-ABI entry points for the harness
├── HashSpecsTests/                    # Lean-side KATs and Plausible properties
│   └── vectors/                       # vendored official vectors, with provenance README
├── harness/                           # Rust cargo workspace, see §4
├── bridges/                           # temporary separate Lake package, see §6
└── docs/                              # Verso book, see §3
    ├── HashSpecsDocs/ (chapters), diagrams/ (TikZ/SVG sources), refs.bib
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
- `UInt32`/`UInt64` lanes, `Vector`, `ByteArray`, and CompPoly `Fast` field representations.
- Must handle multi-megabyte inputs in reasonable time.

**Equivalence.** `theorem Fast.hash_eq_reference : Fast.hash = Reference.hash` for every instance or parameter set.
- **Proof strategy:** per-step lemmas (round function, message schedule, padding), then induction over rounds and blocks.
- **Tools:** `bv_decide` for bit-level steps; CompPoly's ring isomorphisms for field steps.
- **Policy:** no `native_decide`, `sorry` or custom `axiom` in the trust chain of any `Equiv` theorem. `native_decide` is allowed only in tests. Enforced in CI with `#print axioms` checks.

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

---

## 3. Documentation: a Verso book

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
8. **Assurance status.** A table, generated from CI output, listing: KATs passed (count and source), fuzz executions and CPU-hours per oracle, the equivalence theorem and its axiom report, bridges to org specs, and known deviations.
9. **Security notes.** Brief, fully cited pointers to the cryptanalysis and proof literature, such as the CCS 2019 indifferentiability result. No new claims.
10. **References.**

**Diagrams:**
- Original artwork only. Never copy figures from papers or standards. FIPS documents are US-government works, but paper figures are copyrighted, so everything is redrawn.
- Authored as TikZ, or hand-written SVG, in `docs/diagrams/`, and compiled to SVG in CI so the sources stay reviewable.
- Shared style: colour-blind-safe palette, readable in light and dark mode, consistent glyphs for XOR, addition modulo 2ʷ and rotation.
- Stretch goal: interactive round explorers. A Verso page embeds a JS widget driven by worked-example data exported from Lean.

**Citations:**
- One `docs/refs.bib`, with primary sources first: NIST FIPS 180-4 and 202, RFC 7693, the BLAKE3 spec, the Poseidon and Poseidon2 papers (USENIX Sec 2021; AFRICACRYPT 2023), the Rescue-Prime ePrint, the MiMC paper (ASIACRYPT 2016), and the EIP-152 text.
- Each entry includes a DOI or a stable URL and an access date.
- Reference-layer docstrings cite by section number. Verso's bibliography support is checked in Phase 0; the fallback is a small citation extension.

---

## 4. Differential testing harness

### 4.1 Confidence pipeline, per hash

```
official KATs ──► Lean (fast) ◄──► Rust oracles ×≥2  (coverage-guided fuzzing)
                     ▲  proved equal
                Lean (reference) ◄── small-input property tests (Plausible)
```

1. **KATs** run in Lean CI on every PR, from vendored official vectors with a provenance README (source URL and SHA-256 of each file). Sources:
   - NIST CAVP/ACVP for SHA-2, SHA-3 and SHAKE, including the Monte Carlo tests
   - the BLAKE2 reference KATs and the BLAKE3 `test_vectors.json`
   - EIP-152 vectors
   - reference vectors from the Poseidon, Poseidon2 and Rescue authors and from leanSpec
2. **Reference vs fast in Lean** with Plausible. This is useful before the `Equiv` proof exists, and redundant (but cheap) afterwards.
3. **Lean fast vs Rust oracles**, in two modes:
   - **In-process (primary):** `HashSpecs/FFI/Export.lean` exposes `@[export hs_<hash>]` C-ABI functions taking bytes, field-element limbs and parameters. Lake builds a static library. A `hashspecs-sys` Rust crate links it with the Lean runtime, initialises the runtime and the module once (with per-thread initialisation for fuzz workers), and offers safe wrappers. Fuzz targets use `cargo-fuzz` (libFuzzer), and `proptest` drives deterministic CI runs.
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

---

## 5. Phased roadmap

Sizes are relative (S/M/L/XL), not calendar estimates. Each phase ends with explicit exit criteria. **Phase 1 is a deliberately complete vertical slice:** every later hash reuses its pipeline.

### Phase 0: Foundations (M)
- Pin toolchain `v4.34.0` and add CompPoly `v4.34.0-patch2`, Verso, Plausible, doc-gen4 and checkdecls.
- Adopt the module system and linter options. Record a zero-warning baseline and enforce it in CI.
- Settle the Mathlib-free core question from §2.1 by checking the dependency trees of `evm-asm`, `leanerVM`, `clean` and `VCVio`.
- Write `CONTRIBUTING.md` with the spec style guide: naming, citation format, reference and fast layers, the axiom policy, and instance naming.
- `Prelude`: byte, word and endianness utilities and their core `BitVec`/`UInt` lemmas.
- Harness skeleton: a `hashspecs-sys` crate links a trivial `@[export]` function and runs one `cargo-fuzz` target in CI on Linux and macOS.
- Verso skeleton: one chapter containing a compiled TikZ→SVG diagram, a type-checked code block and a bibliography citation, deployed to GitHub Pages.
- Open a discussion with org maintainers (the ArkLib/CompPoly/VCVio leads, the Clean team and the verified-zkevm.org lead) about canonical-upstream intent, naming and the eventual transfer of the repo into the org.
- **Exit:** CI is green end to end on the placeholder, and maintainers have acknowledged the plan.

### Phase 1: SHA-256 vertical slice, then the rest of SHA-2 (L)
- `Construction/MerkleDamgard`, SHA-2 reference (FIPS 180-4 §§4–6), fast layer, `Equiv`, and derivation of the constants (`K`, `H₀`).
- CAVP SHAVS short, long and Monte Carlo KATs. Fuzzing against `sha2` and `aws-lc-rs`, plus streaming-vs-one-shot.
- A Verso chapter with all the elements of §3.
- **Bridges:** `clean` `Specs.SHA256` and `VCVio` `Concrete.Sha2`.
- Then extend to SHA-224, SHA-384, SHA-512 and SHA-512/224 and /256, which should be mostly parameter work.
- **Exit:** all SHA-2 variants pass KATs, reach a set fuzz budget (for example 10⁹ executions per oracle) with no divergence, have axiom-clean `Equiv` theorems, and have a complete chapter.

### Phase 2: SHA-3 / Keccak (L)
- Keccak-p[b, n_r] reference for every b, `Construction/Sponge` with pad10*1, SHA3-224/256/384/512, SHAKE128/256, and Ethereum Keccak-256 with `0x01` padding.
- Proofs: fast-layer `Equiv` for b = 1600, Keccak-p bijectivity, and XOF prefix consistency.
- CAVP SHA3VS KATs, fuzzing against `sha3`, `tiny-keccak` and `alloy`.
- **Bridges:** `clean`, `VCVio`, `zkLean` and `evm-asm`. This is the biggest deduplication win in the org.
- **Exit:** the same criteria as Phase 1, plus bridge PRs opened against all 4 repos.

### Phase 3: BLAKE2 and BLAKE3 (L)
- BLAKE2b and BLAKE2s (RFC 7693, plus the parameter block for key, salt and personalisation), and the BLAKE2b-F compression function with a configurable round count (EIP-152).
- BLAKE3: the compression function, chunk chaining, the binary tree (`Construction/Tree`), the keyed, derive_key and XOF modes, and a proof that streaming equals one-shot.
- **Bridges:** `leanerVM` BLAKE2s, `evm-asm` Blake2f, `clean` BLAKE3.
- **Exit:** the same criteria as Phase 1.

### Phase 4: ZK-friendly hashes I, Poseidon and Poseidon2 (XL)
- **`ZK/Common`:**
  - a generic SPN permutation over a CompPoly field (`[Field F]` for the reference layer, CompPoly `Fast` for the fast layer)
  - power S-boxes x^α with a gcd(α, p−1) = 1 side condition
  - Grain-LFSR constant generation
  - Cauchy MDS generation, plus an MDS check for small t
  - round-number formulas as functions, with a table of the chosen instances
- **Poseidon** (Grassi et al., USENIX Sec 2021): the reference layer as in the paper, and the *optimized* form with sparse matrices and partial-round constant folding as used by circomlib, with `Equiv` between them. This closes the gap the Clean team noted.
  - Instances: circomlib BN254 for t = 2..17 (or the subset in use).
- **Poseidon2** (Grassi, Khovratovich, Schofnegger, AFRICACRYPT 2023): external and internal matrices.
  - Instances: HorizenLabs BN254 t = 3, Plonky3 BabyBear and KoalaBear widths 16 and 24, leanSpec KoalaBear.
- `Construction/FieldSponge`, including the domain separation conventions each ecosystem uses (circomlib's capacity initialisation versus Plonky3's padding-free sponge). Each convention is documented as its own instance.
- **Bridges:** `clean` Poseidon (both of its specs) and `ArkLib` `Data/Hash/Poseidon2`.
- **Exit:** every listed instance passes its authors' vectors, is fuzzed against two oracles, and has axiom-clean `Equiv` theorems.

### Phase 5: ZK-friendly hashes II (XL; partly blocked)
- **Rescue-Prime** (Szepieniec, Ashur, Dhooghe), including the inverse S-box x^{1/α}, and **RPO** (Miden, Goldilocks).
- **MiMC:** MiMC-n/n, the Feistel variant, and circomlib's `MiMCSponge` over BN254.
- **Pedersen hashes** need twisted-Edwards and short-Weierstrass curve arithmetic that CompPoly doesn't provide (ArkLib has BN254 G1 only). Options:
  - co-develop curves (BabyJubJub, Jubjub, the Stark curve) upstream in CompPoly or ArkLib
  - or specify the hash relative to an abstract group, plus concrete instances once the curves exist

  *Decision needed at the start of Phase 5.*
- **Stretch candidates**, each needing a short survey of real-world use first: Anemoi, Griffin, Monolith, Tip5, Reinforced Concrete.
- **Exit:** per hash, the same criteria as Phase 4.

### Phase 6: Hardening, migration, v1.0 (M)
- Upstream migration: the bridge theorems land in the downstream repos, which then `import HashSpecs` and delete their local copies, coordinated with maintainers.
- An external review of the reference layers against the standards. Ideally an independent reader per family, with sign-off recorded in each chapter's assurance table.
- Prebuilt release oleans in CompPoly's style (`preferReleaseBuild`), versioning and a changelog.
- Optional: bridges to the external Lean specs (SymCrypt/Aeneas, Nethermind `LeanCrypto`, Axiom `openvm-fv`), turning "five Keccaks" into one proved-equal family.
- **Exit:** v1.0 tagged, at least 2 org repos migrated, and the docs site published.

**Rough dependency graph:**
```
P0 ──► P1 ──► P2 ──► P3
          └──► P4 ──► P5          P6 after P3 and P4
```
P2/P3 and P4 can run in parallel once Phase 1 has proved the pipeline.

---

## 6. Bridges and migration mechanics

- **Circular-dependency trap.** Once `clean` depends on `hash-specs`, a bridge proof that imports `clean` cannot live in `hash-specs`. So:
  1. Prototype bridges in a separate Lake package, `bridges/`, which depends on both sides and is CI-only and never published.
  2. Upstream each bridge as a PR to the downstream repo. The downstream repo then defines its local spec as ours, or keeps it with the bridge theorem.
- **Bridge statement shape:**
  ```
  theorem Clean.Specs.Keccak256.keccak256_eq (m) : Clean.Specs.Keccak256.hash m = HashSpecs.Keccak.keccak256 m
  ```
  - Representation adapters (`Nat` lanes versus `UInt64`, `Vector` versus `ByteArray`) are stated explicitly and proved as lemmas.
- **Bridges are evidence for both sides.** If a bridge can't be proved, someone has a bug, and the differential harness finds which side it is.
- **Order of migration:** least disruptive first. Leaf consumers (`zkLean` examples, `VCVio` HashSig) go before core dependencies (`clean` gadgets, `ArkLib`).

---

## 7. Open decisions

These don't block Phase 0. Defaults are given in brackets.

1. **Package and namespace name.** [Keep `HashSpecs`, matching the repo.] Revisit if the repo is transferred into the org.
2. **Repo home.** [Develop here, then propose transfer to `Verified-zkEVM` after Phase 1.]
3. **Mathlib-free core split.** [Decide in Phase 0 from consumer dependencies.]
4. **RIPEMD-160.** [Include it, since it's small. It's an EVM precompile and `evm-asm` already has a copy.]
5. **Poseidon and Poseidon2 instance list.** [Instances actually used in the org's targets: circomlib, Plonky3, leanSpec, HorizenLabs.] Confirm against verified-zkevm.org priorities.
6. **Pedersen curve strategy.** [Abstract group first, concrete curves when available.]
7. **PDF output.** [HTML site first; PDF only if Verso's TeX backend is adequate.]
8. **SP 800-185 (cSHAKE, KMAC, TupleHash, ParallelHash).** [Defer to after v1.]

---

## 8. Risks and mitigations

| Risk | Mitigation |
|---|---|
| Linking the Lean runtime into Rust (static linking, initialisation, threads) is fiddly across platforms. | Prove it out in Phase 0 on a trivial export. The subprocess protocol is always available as a fallback. |
| Toolchain churn: CompPoly's `fixedToolchain` forces lockstep bumps. | Track CompPoly tags and keep CI on the exact pin. Small, frequent bumps. |
| `Equiv` proofs over many rounds or large states blow up `bv_decide` or elaboration. | Per-round lemmas plus induction. Avoid unfolding whole permutations. Never fall back to `native_decide` in the trust chain. |
| Correlated oracles, for example XKCP-derived Keccak implementations, hide the same bug. | Record the lineage of each oracle and require one independent implementation per hash. Official KATs act as a third source. |
| ZK hashes are underspecified: "Poseidon" names many incompatible variants. | Explicit instance naming, parameter provenance (repo and commit), and generating constants instead of pasting them. |
| Verso API churn or immature features (citations, TeX). | Pin Verso with the toolchain. Keep diagram sources format-agnostic (TikZ/SVG). Have small local extensions ready. |
| Copyright of diagrams and of text quoted from papers. | Original diagrams only. Quote only short spans, with citations. |
| Trusted computing base of the testing itself: the Lean compiler and runtime, and the C toolchain. | State it in the docs. The `Equiv` proofs are kernel-checked, and only the fast-layer execution relies on the compiler. |
| Social risk: downstream maintainers may not migrate. | Engage them in Phase 0. Bridges deliver value even without migration. Keep the API ergonomic for their representations. |

---

## 9. Definition of done, per hash

A hash is **done** when:
- [ ] The reference spec cites a section of the standard on every definition.
- [ ] Constants are derived and the tables proved equal to the derived values.
- [ ] The fast spec has an `Equiv` theorem, and `#print axioms` shows only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- [ ] All official KATs pass in CI, from vendored vectors with recorded provenance.
- [ ] It is fuzzed against at least 2 independent oracles, past the fuzz budget, with no open divergences.
- [ ] Streaming-vs-one-shot (and XOF prefix consistency, where relevant) is proved or tested.
- [ ] It has a Verso chapter covering every §3 section, with original diagrams and a worked example.
- [ ] Bridge theorems exist for every org spec of the same function, and upstream PRs are open.
- [ ] The build has zero warnings.
