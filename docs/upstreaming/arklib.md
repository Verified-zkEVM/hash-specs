# Upstreaming record: ArkLib

Checked on 2026-10-27 against `Verified-zkEVM/ArkLib` at **`59e5b77`** (2026-10-27, "fix: remove unused admitted coding-theory declarations (#1297)"), and hash-specs at `98c225d`. File:line references are to those commits.

**Summary.**
- **The bug is already fixed upstream.** The external-round-constant indexing bug that ROADMAP.md:338 and `docs/research/poseidon2.md` §4 describe was real. ArkLib PR #1316 (`2817d8c`, merged 2026-10-19) fixed it, and it is no longer present at HEAD.
- **ArkLib now computes a different instance from ours.** It computes the *leanSpec / Plonky3 < 0.6* KoalaBear Poseidon2, while hash-specs ships Plonky3 0.8.0. Both are internally consistent; they differ only in the order in which the Grain constants are assigned to rounds. This was verified by computation (§7).
- **No toolchain bump is needed.** ArkLib is already on v4.35.0, with the same Mathlib and CompPoly pins as hash-specs.
- **The overlap is small.** It is one Poseidon2 file with no production consumers and one test file. The duplex sponge is an abstract, ideal-permutation model with no concrete permutation, so nothing in it can be swapped. Its one hash-shaped hole is `generateTag`, a `sorry` that should be Keccak.

---

## 1. Snapshot

| Item | Value | Evidence |
|---|---|---|
| Repo / SHA | `Verified-zkEVM/ArkLib` `59e5b77` | shallow clone at HEAD |
| Toolchain | `leanprover/lean4:v4.35.0` | `lean-toolchain` |
| Lakefile | `lakefile.toml` | |
| Mathlib | `v4.35.0` → `56a0058` (via VCVio/CompPoly; not required directly) | `lake-manifest.json` |
| CompPoly | `rev = "v4.35.0"` → `06686e4` | `lakefile.toml` `[[require]] CompPoly`; tag `v4.35.0` peels to `06686e4` (`gh api`) |
| VCVio | `v4.35.0` → `88efe97` | manifest |
| Others | doc-gen4 v4.35.0, checkdecls lean4.18.0, cslib v4.35.0, PolyFun `ef4c157` | manifest |
| Module system | Yes. `ArkLib` has `requiresModuleSystem = true`; `ArkLibTest` has `allowNonModules = true` | `lakefile.toml` (lib `ArkLib`, lib `ArkLibTest`) |
| Release tagging | Tags on each `lean-toolchain` change (`leanprover-community/lean-release-tag`) | `.github/workflows/release-tag.yml` |

**Toolchain gap.**
- There is none. ArkLib is on v4.35.0, as are hash-specs and hash-specs-zk.
- Every shared pin is identical: mathlib `56a0058`, batteries `66e4691`, Qq, aesop, plausible, Cli `c24fe60`, CompPoly `06686e4`. Lake should not see any version conflict.
- ROADMAP.md:59 ("ArkLib | Lean v4.34.0") is stale.

**Future bumps.**
- hash-specs must cut a release at each new toolchain before ArkLib can bump.
- ArkLib bumps in lockstep with CompPoly and VCVio, which are Verified-zkEVM repos as hash-specs is, so cutting our release can be part of the same coordinated bump.

**Which package.**
- The bridge in §5 needs only the **core** `hash-specs` package, because `Hash.ZK.Poseidon2.Reference` is in core.
- ArkLib's field is `KoalaBear.Field := ZMod KoalaBear.fieldSize`, a `ZMod` (CompPoly `Fields/KoalaBear/Basic.lean:32`), not CompPoly's Montgomery `KoalaBear.Fast.Field`.
- `hash-specs-zk` would also resolve cleanly (same CompPoly rev), but nothing in ArkLib needs it today.

**Where ArkLib's KoalaBear field comes from.**
- ArkLib already takes it from CompPoly: `ArkLib/Data/Hash/Poseidon2.lean:8` has `public import CompPoly.Fields.KoalaBear`.
- The field moved out of ArkLib in `e127571` "Refactoring CompPoly Out of Arklib (#307)".
- `KoalaBear.fieldSize = 2 ^ 31 - 2 ^ 24 + 1` (CompPoly `Basic.lean:26`). This is literally the same expression as our `Hash.ZK.koalaBear` (`Hash/ZK/Common/Primes.lean:35`), so `KoalaBear.fieldSize = Hash.ZK.koalaBear := rfl` should close it. **Not compiled.**

## 2. Overlap inventory

### 2.1 `ArkLib/Data/Hash/Poseidon2.lean` (692 lines, namespace `Poseidon2`)

The file is in `ArkLib.lean:545`, with `@[expose] public section` (l.27). It is a "translation of leanSpec's Python Poseidon2" from 2025-09-12 (l.14–17).

| Line | Name | Signature / representation | hash-specs counterpart |
|---|---|---|---|
| 37 | `rawConstants16` | `Vector KoalaBear.Field 148`, hex literals in three segments, commented at l.38, 103 and 124: initial external 4×16, internal 20, final external 4×16 | No exact counterpart. The values are Grain output in the **pre-0.6 draw order** (§7.2). Ours is `(Plonky3.samples koalaBear16)`, in 0.8.0 order (`Hash/ZK/Poseidon2/InstanceParams.lean:54,134`). |
| 193 | `RAW_CONSTANTS_24` | `Vector KoalaBear.Field 215`, the same layout for width 24 (l.194, 291, 315) | As above, for `koalaBear24` |
| 415 | `sBoxDegree` | `Nat := 3` | `Plonky3.α` (`koalaBear16 = ⟨koalaBear, 3, 16, 20, …⟩`, InstanceParams.lean:128) |
| 418 | `structure Params` | `width numFullRounds numPartialRounds : Nat`, `internalDiagVectors : Vector F width`, `roundConstants : Vector F (numFullRounds*width + numPartialRounds)`, plus side conditions | `Hash.ZK.Poseidon2.Params F t` (Reference.lean:40), which uses function-valued `CE`/`CI`/`ME`/`MI` |
| 472 | `params16` | (16, 8, 20), with the diagonal written as field fractions (l.476–493) | `Hash.ZK.Poseidon2.koalaBear16`, apart from the constant order. The diagonal is equal to `koalaBearDiag16`, verified in §7. |
| 501 | `params24` | (24, 8, 23) | `koalaBear24`, apart from the constant order. The diagonal is equal to `koalaBearDiag24`, verified. |
| 538 | `m4Matrix` | `Vector (Vector F 4) 4 = [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]` | `plonky3M4` (InstanceParams.lean:81) |
| 548 | `applyM4` | `Vector F 4 → Vector F 4` (`Vector.Matrix.mulVec`, from CompPoly `Data/Vector/Basic.lean:213`) | part of `Fast.External.m4` / `blockCirculant` |
| 567 | `externalLinearLayer` | per-chunk M4, then add column sums; equals `circ(2·M4, M4, …)` | `Reference`: `ME := blockCirculant …` (Reference.lean:75); `Fast`: `.m4`; equivalence lemma `externalM4_eq` (Equiv.lean:112) |
| 594 | `internalLinearLayer` | `sumAll + d_i * s_i`, i.e. `(J + diag d) s` | `onesPlusDiag` (Reference.lean:64), and `onesPlusDiag_mulVec` / `internal_eq` (Equiv.lean:67,83) |
| 604 | `fullRound` | add a width-sized RC chunk, S-box on all elements, external layer | `Reference.externalRound` (Reference.lean:88) |
| 614 | `partialRound` | add the RC to `s[0]`, S-box on `s[0]`, internal layer | `Reference.internalRound` (Reference.lean:93) |
| 625–657 | `numFullRounds_mul_width`, `firstHalfRoundConstants_extract_length`, `partialRoundConstant_index_lt`, `secondHalfRoundConstants_extract_length` | index arithmetic for `permute` | none needed (ours indexes `CE r i`) |
| 661 | `permute` | `(params : Params) → Vector F width → Vector F width`: initial external layer; `Fin.foldl` over half the full rounds with `rcs.extract (i*w) (i*w+w)` (l.670); partial rounds from `rcs.drop` (l.675–680); final full rounds (l.686) | `Hash.ZK.Poseidon2.Reference.permutation` (Reference.lean:97), with the same round structure |

### 2.2 `ArkLibTest/Data/Hash/Poseidon2.lean` (50 lines)

The file was added in #1316. It defines `permuteNat` (l.17–18: map `Nat`s in, `ZMod.val` out) and has five `decide +kernel` examples:

| Width | Input | Lines |
|---|---|---|
| 16 | zero | 20–23 |
| 16 | `0..15` | 25–28 |
| 16 | Plonky3's random vector `894848333, …` | 30–35 |
| 24 | zero | 37–41 |
| 24 | `0..23` | 43–47 |

- The docstring (l.9–13) says these are "Known answers of Plonky3's `default_koalabear_poseidon2_16` and `_24`, whose constants are leanSpec's".
- That holds only for Plonky3 releases before 0.6. The release is not pinned (§7.2).
- hash-specs counterpart: `zk/HashKAT/vectors/poseidon2/kats.json`, which holds Plonky3 0.8.0's vectors (a *different* output for the same random input).

### 2.3 Duplex sponge: `ArkLib/Data/Hash/DuplexSponge.lean` (665 lines)

This file models spongefish's duplex sponge, as of 2025-06-22 (l.13–24).

| Line | Name | Signature / representation | hash-specs counterpart |
|---|---|---|---|
| 34 / 40 | `class Permute α`, `class LawfulPermute α` | `permute : α → α`; the lawful version adds `permuteInv` with left and right inverse proofs | no class. Bijectivity of Keccak-p is proved (`Hash/Keccak/Bijective.lean:272,285,295`); there is none for Poseidon2. |
| 74–102 | `forwardPermutationOracle`, `backwardPermutationOracle`, `permutationOracle`, `*Impl` | VCVio `OracleSpec` wrappers (ideal permutation) | out of scope (security model) |
| 120 | `class SpongeUnit α` | `Zero`, `Serde α ByteArray`, `HasSize α UInt8` (CompPoly classes), plus IO `write`/`read` | none |
| 161 | `class DuplexSpongeInterface U α` | `absorbUnchecked`, `squeezeUnchecked`, `ratchetUnchecked`, `Initialize α (Vector UInt8 32)` | none |
| 196 | `class SpongeSize` | `N R : Nat`, `R < N`, `NeZero R` | the `width`/`rate` arguments of `Hash.FieldSponge.paddingFree` |
| 258 / 278 / 297 | `SpongeState` (a lens `get`/`update`), `CanonicalSpongeState := Vector U N`, and its instance | the instance sets `new := fun _ => 0` (l.299, commented "PROBLEM") | — |
| 322 | `structure DuplexSponge U C` | `state : C`, `absorbPos squeezePos : Fin (R+1)` | none (ours is stateless and list-based) |
| 379 | `start` | an oracle-sampled capacity, with a zero rate | none |
| 419 / 466 | `absorb` (element-wise, the paper's version) / `absorbFast` (chunked, the Rust version) | `OracleComp (forwardPermutationOracle C) _`. **Overwrite mode, with a lazy permutation**: it permutes only when `absorbPos = R` and more input arrives | `Hash.FieldSponge.overwrite`/`absorb` (`Hash/Construction/FieldSponge.lean:46,50`), also overwrite mode, but permuting **eagerly** after each block |
| 502 / 603 / 631 | `absorbUnchecked`, `squeezeUnchecked`, `ratchetUnchecked` | `simulateQ` with a concrete `[Permute C]` | — |
| 515 / 560 | `squeeze` (element-wise), `squeezeInto` (chunked) | permutes when `squeezePos = R`; sets `absorbPos := 0` | the `.take out` of `paddingFree` (FieldSponge.lean:56) |
| 615 | `ratchet` | permute, then zero the rate | none |
| 663 | `instance : SpongeUnit UInt8` | the only concrete unit | — |

`Hash/Construction/Sponge.lean` (the bit-level Keccak sponge with `pad101` and XOR absorb) is a different construction. It is the padded XOR sponge of FIPS 202, not an overwrite duplex, and has no counterpart in ArkLib.

### 2.4 Fiat–Shamir over the duplex sponge (`ArkLib/OracleReduction/FiatShamir/DuplexSponge/*`)

- `Defs.lean` (253 lines) contains message and challenge sizes, permutation-query counts, the `duplexSpongeChallengeOracle` (l.101) and the DSFS prover, verifier and reduction (l.126–253). All of it is generic over `[SpongeUnit U] [SpongeSize]`, and it has no counterpart in hash-specs.
- `Data/Hash/DomainSep.lean` (332 lines) is spongefish's domain-separator string grammar. It has no counterpart.
- `State.lean` (455 lines) contains `HashStateWithInstructions` (l.60) and the `FSVerifierState` and `FSProverState` (l.168, 310).
  - **`generateTag (iopBytes : ByteArray) : Vector UInt8 32 := sorry`** (l.85–87, "TODO: Implement Keccak hashing"). The docstring (l.71–83) quotes spongefish's `Keccak::default()`, `absorb_unchecked` and `squeeze_unchecked` into 32 bytes.
  - `absorb`, `squeeze`, `hint` and `ratchet` on `HashStateWithInstructions` are also `sorry` (l.111, 123, 135, 147).
  - The counterpart for `generateTag` would be a byte-state Keccak-f[1600] duplex. Our `Hash.Keccak.Fast.keccakF : Array UInt64 → Array UInt64` (`Hash/Keccak/Fast.lean:81`) exists, but we expose no byte-state duplex wrapper (§6).
- `Security/*` (9 files, 880 lines) contains security proofs in the ideal-permutation model. They have 12 `sorry`s in total and no concrete hash.

### 2.5 `ArkLib/Commitments/Functional/Basic.lean` (362 lines)

**There is no hash content.** This file holds the abstract functional-commitment interfaces: `KeyGen`, `Commit`, `Opening`, `Scheme`, correctness, binding, extractability and function binding (l.52–348), all over a generic `oSpec`. `grep -i 'hash\|merkle\|sponge'` finds nothing. Nothing in it needs a bridge.

### 2.6 Other hash code in ArkLib

`grep -rli 'poseidon|keccak|sha256|sha3|blake'` over `ArkLib/`, `ArkLibTest/`, `blueprint/` and `scripts/` returns only the Poseidon2 files and `State.lean` (the Keccak TODO). There is no SHA, BLAKE or Merkle-hash instantiation. `OracleReduction/BCS/Basic.lean` mentions Merkle trees only in prose.

## 3. How it is used

| Definition | Consumers | Kind |
|---|---|---|
| `Poseidon2.*` (Poseidon2.lean) | **None in production.** It is imported only by `ArkLib.lean:545` (the umbrella) and `ArkLibTest/Data/Hash/Poseidon2.lean:7`. | executable spec, tested by KAT (5 `decide +kernel` examples) |
| `DuplexSponge`, `SpongeUnit`, `SpongeSize`, `Permute`, … | 14 files (`DomainSep.lean`, `FiatShamir/Basic.lean`, `FiatShamir/DuplexSponge/{Defs,State}.lean`, and 9 `Security/*.lean`) | an abstract model; proofs run against an *oracle* permutation, so there is no spec to re-target |
| `generateTag` | `HashStateWithInstructions.new` (State.lean:96–99) | an executable stub (`sorry`) |

**Call sites that change.**
- If Poseidon2 is replaced, 0 production call sites change and 1 test file changes.
- For the sponge, nothing changes until someone instantiates a concrete permutation.
- No correctness proof in ArkLib targets `Poseidon2.permute`. The bridge therefore only adds evidence and removes nothing.

## 4. Representation gaps and adapter lemmas

| Gap | Statement needed | Who provides it |
|---|---|---|
| Field identity | `theorem KoalaBear.fieldSize_eq : KoalaBear.fieldSize = Hash.ZK.koalaBear := rfl` (both are `2 ^ 31 - 2 ^ 24 + 1`), so that `KoalaBear.Field = ZMod Hash.ZK.koalaBear` holds by `rfl`/`Eq.mpr` | ArkLib. This is a one-liner; alternatively hash-specs-zk, which already imports CompPoly. **Not compiled.** |
| Constant table → `Params` | ArkLib's flat `Vector F (R_F·t + R_P)`, laid out `ei ‖ it ‖ ef`, versus our `CE : ℕ → Fin t → F`, `CI : ℕ → F` | ArkLib (definition `Params.toSpec` in §5). It is specific to ArkLib's layout. |
| External layer | `externalLinearLayer params s = Vector.ofFn ((blockCirculant M4).mulVec (s[·]))`, where `M4 := Matrix.of fun a b => m4Matrix[a][b]` | ArkLib, reusing hash-specs' `externalM4_eq`/`blockMul_get` (Equiv.lean:102,112) on the `Fast` side. hash-specs could export a lemma `blockCirculant_mulVec_eq_chunked` in "M4 per chunk, then add column sums" form; this is generic, so worth adding. |
| Internal layer | `internalLinearLayer params s = Vector.ofFn ((onesPlusDiag d).mulVec (s[·]))` | ArkLib, via `onesPlusDiag_mulVec` (Equiv.lean:67) |
| Loops | `Fin.foldl n f x = (List.range n).foldl (fun x i => f x ⟨i, _⟩) x` | Mathlib/Batteries probably already has a form of this. **Unverified.** |
| Out-of-range constants | `Reference.permutation P` reads `CE r` only for `r < RF` and `CI r` only for `r < RP`: a lemma `Reference.permutation_congr` | **hash-specs** (generic; it is missing, §6) |

## 5. Proposed bridge theorems

These are sketches. The names on our side were checked in our source; the ArkLib-side definitions are proposals and **have not been compiled**.

```lean
import ArkLib.Data.Hash.Poseidon2
import Hash.ZK.Poseidon2.Instances   -- core hash-specs; Mathlib only

namespace Poseidon2

/-- ArkLib's parameters as hash-specs reference parameters (table laid out `ei ‖ it ‖ ef`). -/
def Params.toSpec (params : Params) : Hash.ZK.Poseidon2.Params KoalaBear.Field params.width where
  α  := sBoxDegree
  RF := params.numFullRounds
  RP := params.numPartialRounds
  CE r i := if r < params.halfNumFullRounds then
      params.roundConstants.toArray.getD (r * params.width + i) 0
    else params.roundConstants.toArray.getD
      (params.halfNumFullRounds * params.width + params.numPartialRounds
        + (r - params.halfNumFullRounds) * params.width + i) 0
  CI r := params.roundConstants.toArray.getD (params.halfNumFullRounds * params.width + r) 0
  ME := Hash.ZK.Poseidon2.blockCirculant (Matrix.of fun a b => m4Matrix[a][b])
  MI := Hash.ZK.Poseidon2.onesPlusDiag (params.internalDiagVectors[·])

/-- (B1) ArkLib's Poseidon2 is the Poseidon2 of the paper, as specified by hash-specs. -/
theorem permute_eq_spec (params : Params) (s : Vector KoalaBear.Field params.width) :
    permute params s = Hash.ZK.Poseidon2.Reference.permutation params.toSpec s := by
  sorry -- structural: unfold both, match the three loops, use the layer lemmas of §4

/-- (B2a) If ArkLib keeps leanSpec's constants: equal to a hash-specs pre-0.6 instance
(prerequisite H1 below; names provisional). -/
theorem permute_params16 (s : Vector KoalaBear.Field 16) :
    permute params16 s =
      Hash.ZK.Poseidon2.Plonky3.permutationPre06 Hash.ZK.Poseidon2.koalaBear16 s := by
  sorry -- (B1) + `Reference.permutation_congr` + the constant tables equal by `decide +kernel`

/-- (B2b) If ArkLib switches to Plonky3 ≥ 0.6 (= hash-specs today): no hash-specs change needed. -/
theorem permute_params16' (s : Vector KoalaBear.Field 16) :
    permute params16' s = Hash.ZK.Poseidon2.Plonky3.permutation Hash.ZK.Poseidon2.koalaBear16 s

end Poseidon2
```

**Difficulty.**
- **B1 is a structural proof of medium size**, about 150–300 lines. The algorithms are already round-for-round equal (§7.3), so the work is in the encodings:
  - CompPoly's `Vector.Matrix.ofFlatten`/`transpose`/`flatten` with `cast`s, against our `Matrix.mulVec` over `Fin t`;
  - `Fin.foldl` against `List.foldl` over `List.range`;
  - `Vector.extract`/`drop` arithmetic against `CE r i`.
  hash-specs' `Equiv.lean` already proves the matrix facts for its own `Fast` layer, so a route through `Fast.permutation` and `permutation_eq` (Equiv.lean:187) may be shorter.
- **B2 is cheap once B1 exists.**
  - The constant tables are kernel-checkable. Equality of ArkLib's tables (both widths) with the pre-0.6 Grain draw took **about 7.5 s with `decide +kernel`**, axioms `[propext]` only (§7.4).
  - The diagonals reduce to `ZMod` arithmetic, which `decide` handles.
  - B2 needs only `decide` and no `native_decide`, which matters because ArkLib forbids native-compiler trust (CONTRIBUTING.md:66–70).
- **Sponge.** ArkLib has no concrete sponge yet, so there is no bridge to propose now. A future lemma that is true by inspection of the code, with the statement checked by reading it and not by Lean, would be:

  ```lean
  -- xs ≠ [] and n ≤ R; state starts at 0 with absorbPos = 0, squeezePos = R
  (squeezeUnchecked (absorbUnchecked s₀ xs.toArray) (Array.replicate n 0)).2.toList =
    Hash.FieldSponge.paddingFree (Hash.FieldSponge.onList Permute.permute) N R n xs
  ```

  - ArkLib's lazy permutation plus the permutation forced at squeeze is equivalent to Plonky3's eager permute-after-each-block.
  - They differ on **empty input**: ArkLib permutes the zero state, while `paddingFree` returns zeros.
  - They also differ for `n > R`, where ArkLib re-permutes and Plonky3's sponge has no multi-block squeeze.
  - Difficulty: medium. The proof needs `simulateQ` lemmas from VCVio and well-founded recursion on `absorbFast`.

## 6. Gaps in hash-specs

1. **The leanSpec / Plonky3 < 0.6 KoalaBear instances (widths 16 and 24).**
   - This is what ArkLib computes today.
   - It is cheap to add: a `Plonky3.samplesPre06` that draws `R_F·t` external constants, then `R_P` internal ones. My scratch `legacySamples` in `evidence/arklib/Kernel.lean` is 5 lines. The instance also needs a `permutationPre06` and `fastParams` variant.
   - ArkLib's five KATs (§2.2) can be vendored as its vectors.
   - It is needed only if ArkLib keeps leanSpec's constants (open question Q1).
2. **`Reference.permutation_congr`**: the permutation depends only on `CE r` for `r < RF` and on `CI r` for `r < RP`. This is generic and needed for any bridge from a table-based spec.
3. **The external layer in "chunked M4, then add column sums" form** (§4). This is generic and optional.
4. **Kernel-checked constants for the 31-bit instances.**
   - Our Poseidon2 README (`Hash/ZK/Poseidon2/README.md:178`) says the constants are "checked … by computation, not in the kernel", and `Grain.lean:30` says something similar.
   - For the KoalaBear instances, the kernel evaluates Grain in a few seconds (§7.4), so `theorem koalaBear16_constants : koalaBear16.samples = (…literal table…) := by decide +kernel` is feasible. The infeasibility claim holds for BN254 (`Hash/ZK/Poseidon/README.md:140`) but not here.
   - A downstream bridge would then not depend on trusting our Grain implementation.
5. **A byte-state Keccak-f[1600] permutation for spongefish's `generateTag`.**
   - Something like `Hash.Keccak.keccakFBytes : Vector UInt8 200 → Vector UInt8 200` (little-endian lanes), with an equation to `Fast.keccakF`.
   - A spongefish-compatible overwrite duplex (`N = 200`, `R = 136`) would also be needed. **Unverified**: these are spongefish's parameters as I recall them; I did not check them against spongefish source.
   - It could be bridged into ArkLib's `[Permute (Vector UInt8 200)]`. `LawfulPermute` needs a `permuteInv` function; our Keccak-p is proved bijective (`Bijective.lean:272`) but has no computable inverse.
6. **Poseidon2 bijectivity / inverse.** We have none, and it is needed for a `LawfulPermute` instance on Poseidon2. The linear layers are invertible and the S-box `x³` is a bijection on KoalaBear (gcd(3, p−1) = 1), so this is a plausible addition.

## 7. Discrepancies (checked concretely)

The scratch files are in `evidence/arklib/`:
- `ArkP2.lean`: ArkLib's l.29–691 verbatim, plus drivers;
- `Legacy.lean`, `Bridge.lean`, `Kernel.lean`;
- ArkLib at `dca9038` (before #1316), compared against, was fetched from GitHub and is not kept.

They were run with the hash-specs v4.35.0 toolchain against CompPoly `06686e4`, the same rev ArkLib pins.

### 7.1 The ROADMAP's "ArkLib indexes the external round constants incorrectly" claim is stale

- The bug was real. Before #1316, `permute` took `rcs.extract rc_idx (rc_idx + params.width)`, so round `i` read the window starting at `i` and not at `i·w`.
  - Re-running that indexing on the pre-#1316 table (fetched from `dca9038`) reproduces `docs/research/poseidon2.md`'s `[1237797974, 1287852510, 2019029484, …]` on Plonky3's random width-16 input.
- **It was fixed by ArkLib #1316** (`2817d8c`, 2026-10-19, "fix(hash): Poseidon2 round constants in leanSpec's order, full rounds strided by the width", by `mitschabaude-bot`, found while proving CompStark's Poseidon2).
  - HEAD now reads `rcs.extract (rc_idx * params.width) (rc_idx * params.width + params.width)` (Poseidon2.lean:670, 686).
  - The same PR also **reordered the tables**.
- **At HEAD, ArkLib's `permute` passes all five of its KATs** when executed. It is correct relative to its stated reference. **No issue needs filing about indexing.**

### 7.2 ArkLib and hash-specs implement different KoalaBear instances

On Plonky3's random width-16 input `[894848333, 1437655012, …]`:

| Implementation | Output |
|---|---|
| ArkLib HEAD `permute params16` | `[190453639, 458899855, 383789123, …]` (= ArkLib's test, l.33) |
| hash-specs `HashZK.Poseidon2.koalaBear16` | `[1934285469, 604889435, 133449501, …]` (= Plonky3 0.8.0 KAT in our `kats.json`) |

The zero state at widths 16 and 24 also differs. The cause is entirely the constant order:
- Grain emits one stream `g`. Plonky3 0.8.0, HorizenLabs and hash-specs assign `g[0:4t]` to the initial external rounds, `g[4t:4t+R_P]` to the internal rounds and the rest to the final external rounds.
- Plonky3 < 0.6 and leanSpec assign `g[0:4t]`, then `g[4t:8t]` to the final external rounds and the rest to the internal rounds (README.md:116).
- ArkLib's HEAD tables are exactly the old assignment laid out `ei ‖ it ‖ ef`. This was checked for both widths, in Python and with `decide +kernel`.
- Our `Fast.permutation` with the old draw order reproduces all five ArkLib KATs (`Legacy.lean`).

Before #1316, ArkLib's tables were the raw Grain stream (checked against the `dca9038` blob). That is exactly Plonky3 0.8.0's `ei ‖ it ‖ ef`.
- **With only the indexing fixed, ArkLib would have matched hash-specs and Plonky3 0.8.0.** Old tables plus fixed indexing gives `== ours` → `true`.
- #1316 chose leanSpec's order instead. `docs/research/poseidon2.md` §4 ("constants … exactly current Plonky3") describes the pre-#1316 file accurately but is now outdated.

ArkLib's test docstring ("Plonky3's `default_koalabear_poseidon2_16`") does not pin the Plonky3 version. Since Plonky3 0.6 that name computes the other permutation, so the docstring is ambiguous. This is the one thing worth raising upstream (draft below).

### 7.3 Everything else agrees

| Component | Result |
|---|---|
| Diagonals | Both widths: ArkLib's `internalDiagVectors` equal `(koalaBearDiag{16,24}.getD i (dy 0)).val` for every `i` (evaluated). |
| M4 | Identical. |
| S-box | Identical (3). |
| Round counts | Identical: (8, 20) and (8, 23). |
| Round structure | Identical: initial `M_E`, then 4 full, `R_P` partial, 4 full. |
| Internal-layer convention | Identical (`J + diag d` = our `onesPlusDiag`). |
| Overall | hash-specs' **`Reference.permutation`**, instantiated with ArkLib's tables (`Bridge.lean`, `refParamsOfTable`), reproduces ArkLib's KATs. So B1 (§5) is true on these inputs. |

### 7.4 Kernel cost of the constants

`theorem ark16_eq : ark16 = <legacy Grain draw, ei‖it‖ef>` and `ark24_eq`, both `by decide +kernel`, take **7.5 s wall** in total and use axioms `[propext]` (`Kernel.lean`).

### 7.5 Spongefish fidelity

These are within ArkLib and noted for completeness.

| Item | Detail |
|---|---|
| IV ignored | `CanonicalSpongeState`'s `Initialize` ignores the IV (`new := fun _ => 0`, DuplexSponge.lean:297–302, marked "PROBLEM"). Spongefish seeds the state from the 32-byte tag. The exact spongefish layout is **unverified**. |
| Empty-input absorb | `absorbFast` on empty input still sets `squeezePos := R`, so the next squeeze permutes. Plonky3's `PaddingFreeSponge` on empty input does not permute. These are different conventions, not bugs. |

### 7.6 hash-specs environment issues found while running this

These are build-cache issues, not repo bugs.

- **Stale `HashZK` olean.** The root `.lake/build/lib/lean/HashZK.olean` is a stale **v4.34.0** olean left from before the package split. It shadows `zk/.lake/build` on `LEAN_PATH`, so `cd zk && lake env lean foo.lean` fails with "incompatible header". The workaround was to prepend `zk/.lake/build/lib/lean` and call `lean` directly. Deleting the stale root `HashZK*` build outputs would fix it.
- **Stale CompPoly oleans.** `.lake/packages/CompPoly` had stale v4.34 oleans for `CompPoly.Fields.KoalaBear` (the umbrella) and `CompPoly.Data.Vector.Basic`. Those modules are not imported by hash-specs.
  - I ran `lake build CompPoly.Data.Vector.Basic CompPoly.Fields.KoalaBear` in `zk/`. This touched only build artifacts under `.lake/`.

## 8. PR plan

**ArkLib contribution rules.**
- Titles follow `<type>(<scope>): <subject>`, imperative, lower case, with no trailing dot (CONTRIBUTING.md:31–51); recent examples are `fix(hash): …` and `feat(module-system): …`. The description gives the motivation, the contrast with previous behaviour, and `Closes #…`.
- Before a PR merges:
  - **no new `sorry`/`sorryAx`**;
  - only `propext`/`Classical.choice`/`Quot.sound`;
  - **no native-compiler trust**, so `decide +kernel` is fine and `native_decide` is not;
  - `./scripts/validate.sh` passes, with zero warnings including test warnings;
  - suppressing a linter is rejected by a build plugin (CONTRIBUTING.md:59–85).
- Tests go in `ArkLibTest/`, mirroring the production path.
- Process: CONTRIBUTING.md:25 asks for a discussion or issue first.
- Review: there is no CODEOWNERS file. The AI reviewer runs only when a maintainer comments `/review` (`.github/workflows/review.yml`).
- AI use: there is no AI-disclosure rule. `AGENTS.md` is the canonical agent guide, and #1316 itself came from a bot account.
- Open PRs touching these files:
  - #469 "feat(dsfs): statements of Section 5" and #848 "feat(dsfs): prove Theorems 6.1 and 6.2" both modify `ArkLib/Data/Hash/DuplexSponge.lean` and `FiatShamir/DuplexSponge/*`; both were last updated 2026-09-17. **Avoid editing DuplexSponge.lean until they land or close.**
  - Nothing open touches Poseidon2.
  - `gh issue list --search Poseidon2` finds only #625 (closed, a leanSig/XMSS proposal).

### Prerequisites in hash-specs

| # | Change | Size | Notes |
|---|---|---|---|
| H0 | Correct ROADMAP.md:59 (ArkLib is on v4.35.0) and :338 ("indexes incorrectly" is now "fixed in ArkLib #1316; ArkLib implements the leanSpec/pre-0.6 instance"); add a dated note to `docs/research/poseidon2.md` §4 | XS | documentation only |
| H1 | *(only if Q1 = keep leanSpec)* `Plonky3.samplesPre06`, `Plonky3.permutationPre06`, `fastParams` variant, `HashZK` and `Raw` wrappers if wanted; vendor ArkLib's 5 KATs with their provenance | S (~60 lines + KATs) | the KAT source should be pinned to a Plonky3 release before 0.6 or a leanSpec commit. ArkLib's #1316 cites leanSpec `7d16d18` for the constants. |
| H2 | `Reference.permutation_congr` (§6.2) | S | generic |
| H3 | Kernel theorems equating the KoalaBear (and BabyBear) Grain samples with literal tables (§6.4); update the README claims | S | about 4 s per instance, no new axioms |
| H4 | *(later)* byte-state Keccak-f[1600] and a spongefish-compatible duplex (§6.5) | M | needs a spongefish oracle in `harness/` |

### PRs to ArkLib (incremental)

**A1. `feat(hash): prove Poseidon2.permute equals the hash-specs reference permutation`**
- Lakefile: add the following to `lakefile.toml`, then `lake update hash-specs` (which adds one manifest entry; every transitive pin already matches):
  ```toml
  [[require]]
  name = "hash-specs"
  git = "https://github.com/Verified-zkEVM/hash-specs"
  rev = "v4.35.0-patch1"   # or the release carrying H1/H2
  ```
- Files:
  - new `ArkLib/Data/Hash/Poseidon2/Spec.lean` (or `Poseidon2Spec.lean`), holding `Params.toSpec`, B1, and B2a or B2b;
  - `ArkLib.lean`, for the import;
  - `ArkLibTest/Data/Hash/Poseidon2.lean`, adding `#print axioms`-style acceptance for B1 and B2.
- Deleted: nothing. Kept: everything.
- Proof rework: none. These are new proofs only.
- Size: M, about 200–400 lines.
- Risks:
  - The import graph widens. hash-specs is Mathlib-only and ships prebuilt oleans (`preferReleaseBuild`), but CI time on a cold cache is **unverified**.
  - `check-imports.sh` requires every file to be imported by `ArkLib.lean`.
  - The build plugin's linter policy applies only to ArkLib's own sources.

**A2. `refactor(hash): define the KoalaBear Poseidon2 parameters from hash-specs`**
- Replace `rawConstants16`/`RAW_CONSTANTS_24` (about 400 lines of literals, l.37–412) with the hash-specs instance, keeping `Poseidon2.permute`/`params16`/`params24` as thin wrappers or `@[deprecated]` aliases.
- Alternatively, keep ArkLib's executable code and state only `params16.toSpec ≈ hash-specs instance` (B2).
- Proof rework: none. Nothing downstream uses Poseidon2.
- Size: S–M.
- Risk: the existing `decide +kernel` KATs (about 25 s according to #1316's description) would then also evaluate Grain in the kernel, plus our `Reference` matrix code if `permute` is redefined through it. Kernel time is **unverified**; keep `permute`'s own code to stay safe.

**A3 (optional). `fix(test): pin the Plonky3 release of the Poseidon2 known answers`**
- A docstring-only change to `ArkLibTest/Data/Hash/Poseidon2.lean:9–13`. It can be folded into A1.

**A4 (later, after H4 and after #469/#848 settle). `feat(dsfs): implement generateTag with Keccak-f[1600] from hash-specs`**
- This closes the `sorry` at `State.lean:87`.
- It needs a concrete `Permute (Vector UInt8 200)` and probably the `Initialize` IV fix (§7.5).
- Size: M. Risk: it touches files that open PRs also modify.

### Draft issue text

This draft is **not filed**. There is no indexing bug left to report; this is the remaining ambiguity.

> **Title:** Poseidon2 (KoalaBear): pin which Plonky3/leanSpec instance `params16`/`params24` implement
>
> Since #1316, `Poseidon2.permute` matches the known answers in `ArkLibTest/Data/Hash/Poseidon2.lean`. Those answers come from the pre-0.6 Plonky3 KoalaBear instance (leanSpec's constant order: Grain samples assigned to initial external, then final external, then internal rounds). Plonky3 ≥ 0.6 (commit `0056fa83`, shipped in 0.8.0) assigns the same Grain stream to initial external, internal, final external. The function `default_koalabear_poseidon2_16` therefore now computes a different permutation. On Plonky3's random test vector `[894848333, 1437655012, …]`, 0.8.0 returns `[1934285469, 604889435, 133449501, …]`, while ArkLib returns `[190453639, 458899855, 383789123, …]`.
>
> Neither is wrong, but the test docstring names `default_koalabear_poseidon2_16` without a version. Could we (a) pin the Plonky3 release or leanSpec commit the vectors come from, and (b) decide which instance ArkLib intends to track? leanSpec itself has since moved to Poseidon1. If it is current Plonky3, the pre-#1316 tables (raw Grain order) with #1316's indexing fix give exactly Plonky3 0.8.0.
>
> For cross-checking: `Verified-zkEVM/hash-specs` specifies Plonky3 0.8.0's KoalaBear Poseidon2 (`Hash.ZK.Poseidon2.koalaBear16/24`), with Plonky3 KATs and differential tests. Instantiated with ArkLib's tables, its reference permutation reproduces all five of ArkLib's known answers.

## 9. Open questions for the maintainers

1. **Which KoalaBear instance should ArkLib track?**
   - Option one is leanSpec / Plonky3 < 0.6, today's choice. It needs H1 in hash-specs.
   - Option two is current Plonky3, which hash-specs already has. It needs ArkLib's tables reverted to Grain-stream order, or replaced with hash-specs'.
   - Which downstream user (CompStark? leanSig, #625?) fixes the answer?
2. Is a hash-specs dependency acceptable for `ArkLib.Data.Hash`, given that the import is Mathlib-only and the pins are identical? Or should the bridge live in a separate test-only library (`ArkLibTest`) to keep the production import graph unchanged?
3. Should ArkLib's sponge layer get a concrete instantiation: Poseidon2 over KoalaBear and/or spongefish's Keccak? If so, should hash-specs provide spongefish's duplex as a *construction* (§6.5) for ArkLib to bridge to its `DuplexSponge` by a `simulateQ` lemma?
4. Is the `Initialize … := fun _ => 0` placeholder (DuplexSponge.lean:299) meant to be replaced by spongefish's IV layout, which `generateTag` needs?
5. Release coordination: should hash-specs cut its toolchain release in the same window as CompPoly and VCVio, so that ArkLib's bumps are not blocked?

---

## Appendix: CompPoly (`eco/CompPoly`, HEAD `9be21b0`, 2026-10-27, v4.35.0)

CompPoly has **no hash-function code**. `grep -rli 'poseidon|keccak|sha256|blake|sponge|merkle'` over the `.lean` sources finds only prose and serialization helpers. The hash-adjacent pieces are:
- the `Serialize`/`Deserialize`/`Serde` and `HasSize` classes (`CompPoly/Data/Classes/{Serialize,HasSize}.lean`), which ArkLib's `SpongeUnit` builds on;
- byte → field challenge decoding for byte sponges (`CompPoly/Data/Bytes/Bias.lean`, `CanonicalNat.ofBytesModOrder`, with spongefish's 2⁻¹²⁸ bias margin);
- `Data/Bytes/Vector.lean` and `Fields/Extension/Bytes.lean`, which encode field and extension elements as bytes;
- `Fields/Binary/BF128Ghash`, the GHASH field GF(2¹²⁸) of AES-GCM. This is a field, not a hash.

The KoalaBear, BabyBear and BN254 fields that hash-specs-zk uses come from here. ArkLib pins CompPoly `v4.35.0` = `06686e4`, the same commit as hash-specs-zk; CompPoly HEAD is later (`9be21b0`). No CompPoly PR is needed for this adoption.
