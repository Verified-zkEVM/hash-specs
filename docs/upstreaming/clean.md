# Upstreaming record: clean

Scope: every hash spec in `Verified-zkEVM/clean`: Keccak, SHA-256, BLAKE3 and Poseidon. That
covers `Clean/Specs/*`, the circuits proved against them (`Clean/Gadgets/{Keccak,SHA256,BLAKE3}`,
`Clean/Tables/{KeccakInductive,BLAKE3/*}` and `Clean/Circomlib/Poseidon.lean`), and the open PRs
that touch them (#465, #487, #489, #492).

**Bottom line.**
- clean has the most hash circuits in the org: 34 `FormalCircuit`/table specs (10 Keccak, 10 SHA-256, 8 BLAKE3, 6 Poseidon) are proved against
  its own Nat-valued specs.
- **Bridging is the right approach; re-proving is not.** Every circuit is proved against a sub-step
  of clean's spec (θ, ρπ, χ, σ₀, Ch, G, round, …). Re-targeting the circuits to `Hash.*` would mean
  re-proving all of them. A bridge from the *top-level* clean spec to `Hash.*` costs a few hundred
  lines and touches no circuit.
- **Keccak-f bridge: proved.** I proved `Lanes.permutation (ofFast a) = ofFast
  (Hash.Keccak.Fast.keccakF a)` against our v4.35.0 build: 95 lines, no `sorry`, no warnings,
  standard axioms only. `Lanes` is the BitVec view of clean's Nat-lane spec that open PR #489 adds
  and proves equal to `keccakPermutation` (Appendix A).
- **Two behavioural discrepancies, both on clean's side.**
  1. **Keccak sponge.** clean's `absorbBlock` XORs the block into the wrong lanes, so
     `absorbBlocks` is *not* the Keccak-256 absorb under any block encoding. The table's statement
     ("keccak-hashing some list of input blocks") is therefore stronger than what is proved.
  2. **BLAKE3 chunk.** `processChunk` drops the mode flags on every block except the last.
- SHA-256, BLAKE3 `compress`, and Poseidon t=2..5 all agree with hash-specs on every input tested.
- **Blockers.**
  - Toolchain: clean is on v4.33.1. Draft PR #487 moves it to v4.35.0, with the same Mathlib
    commit as ours.
  - Poseidon: clean specs only circomlib's *optimized* algorithm (folded constants, sparse
    matrices). hash-specs has no optimized form and no equivalence theorem, so the Poseidon bridge
    is hard.

**Priority: high for Keccak, SHA-256 and BLAKE3** once #487 lands. **Medium for Poseidon**, which
needs hash-specs work first.

## 1. Snapshot

| Item | Value |
|---|---|
| Repo | `Verified-zkEVM/clean`, HEAD `0d76409` (2026-10-26, "Merge pull request #446 …"), read 2026-10-27 |
| Toolchain | `leanprover/lean4:v4.33.1` (`lean-toolchain`) |
| Pins | `lakefile.lean:38-39`: Mathlib `v4.33.1` (manifest `0df444a`), CompPoly `v4.33.1` (manifest `a09455a`). No other direct dependencies. |
| Lakefile format | `lakefile.lean`. `requiresModuleSystem := true` on `Clean` (`lakefile.lean:13-15`). |
| Module system | **Yes**: every file is `module` / `@[expose] public section`, the same as hash-specs. |
| CI | `.github/workflows/ci.yml` runs `lake build --wfail` (l.24), `lake build CleanTests` (l.28), the Rust-artifact checks and the Plonky3 tests. `release-tag.yml` tags each toolchain. |
| CONTRIBUTING / CODEOWNERS | None. `AGENTS.md` = `CLAUDE.md` (309 lines, AI-agent context; no disclosure rule). Branch protection is not visible through the API (404). In practice `mitschabaude` reviews and approves (e.g. #460). |
| Toolchain gap | v4.33.1 → v4.35.0 (2 minor releases) |

**Does adoption force a toolchain bump? Yes, and one is already under way.**
- Draft PR #487 "chore: Lean v4.35.0, Mathlib and CompPoly bump" (`mitschabaude-bot`, head
  `92fb068`, updated 2026-10-26) moves clean to `v4.35.0` with Mathlib `v4.35.0` = `56a0058`.
  That is exactly our manifest's Mathlib rev.
- It pins CompPoly to a **fork** commit, `mitschabaude-bot/CompPoly@7596b8e` (PR #487
  `lakefile.lean:31-34`), for CompStark.
- This does not conflict with hash-specs: everything clean needs (Keccak, SHA-2, BLAKE3, and
  `Hash.ZK.Poseidon.Circom` over `ZMod bn254`) is in the **core** `hash-specs` package, which
  requires Mathlib only. The `hash-specs-zk` package, which requires CompPoly, is not needed.
- **Recommendation:** wait for #487, then require `v4.35.0-patch1`. Cutting a hash-specs release
  at v4.33.1 is not worth it, because #487 is close.

## 2. Overlap inventory

Representation legend:
- **Nat-word**: `ℕ`, with an implicit `< 2^32` or `< 2^64` invariant that only the circuits'
  `Normalized` hypotheses enforce.
- **clean index**: Keccak lane `(x, y)` at `Vector` index `5x + y`. hash-specs and FIPS 202 use
  `x + 5y`.

### Keccak (`Clean/Specs/Keccak256.lean`, 204 lines)

| file:line | name | signature / representation | hash-specs counterpart |
|---|---|---|---|
| 8 | `roundConstants` | `Vector UInt64 24` | `Hash.Keccak.roundConstants : List Nat` (`Constants.lean:40`); `Fast.roundConstantWords` |
| 23 | `bits2bytes` | `ℕ → ℕ`, unused | none needed |
| 26 / 35 / 44 / 73 | `thetaC` / `thetaD` / `thetaXor` / `theta` | `Vector ℕ 25 → …`, Nat lanes, clean index | `Hash.Keccak.θ` (`KeccakP.lean:74`); `Fast.theta` (`Fast.lean:41`) |
| 78 | `rhoPi` | ρ then π, fused, clean index | `π ∘ ρ` (`KeccakP.lean:94,99`); `Fast.pi ∘ Fast.rho` |
| 107 | `chi` | uses `not64` | `χ` (`KeccakP.lean:104`); `Fast.chi` |
| 136 | `iota` | `Vector ℕ 25 → UInt64 → Vector ℕ 25` | `ι 6` (`KeccakP.lean:130`); `Fast.iota` |
| 139 | `keccakRound` | | `Rnd 6` (`KeccakP.lean:134`); `Fast.round` |
| 145 | `keccakPermutation` | `Vector ℕ 25 → Vector ℕ 25` | `Fast.keccakF : Array UInt64 → Array UInt64` (`Fast.lean:81`); `keccakF 6` on bits |
| 148-149 | `CAPACITY := 8`, `RATE := 17` (lanes) | Keccak-256 / SHA3-256 rate only | `rate` parameter, 136 bytes, of `Fast.sponge` |
| 152 | `initialState` | zeros | `Array.replicate 25 0` inside `Fast.sponge` |
| 154 | `absorbBlock` | XOR `block[i]` into `state[i]` for `i < 17`, then permute. **Wrong lanes (§7.1).** | `Fast.absorbBlock` (`Fast.lean:94`), on bytes |
| 160 | `absorbBlocks` | `List (Vector ℕ 17) → Vector ℕ 25` | the fold inside `Fast.sponge` (`Fast.lean:110-114`), not exposed by name (§6) |
| (none) | no padding, no squeeze, no byte-level hash | | `Hash.keccak256` |
| `Clean/Utils/Bitwise.lean:11,25,37` | `not64`, `rotRight64`, `rotLeft64` | Nat, root namespace; correct only for `x < 2^64` | `UInt64` ops / `BitVec.rotateLeft` |
| `Clean/Specs/keccak.py` | Python oracle | **correct** (transposes at l.202) | (n/a) |
| PR #489 `Clean/Specs/Keccak256BitVec.lean` | `Lanes := Fin 5 → Fin 5 → BitVec 64`, `Lanes.permutation`, `toState : Lanes → Vector ℕ 25` (index `5x+y`), `keccakPermutation_toState` | open, base `two-row-components` | `Hash.Keccak.State 64` via `getLsbD` (bridged, Appendix A) |

### SHA-256 (`Clean/Specs/SHA256.lean`, 261 lines)

| file:line | name | representation | counterpart |
|---|---|---|---|
| 16 / 36 | `K : Vector UInt32 64`, `H0 : Vector ℕ 8` | | `Hash.SHA2.K256`, `initialHash256` (`Constants.lean:39,51`) |
| 41-57 | `not32`, `lowerSigma0/1`, `upperSigma0/1`, `Ch`, `Maj` | Nat words | `Reference.{smallSigma,bigSigma,Ch,Maj}` (`Reference.lean:90-102`) |
| 61 | `sha256Round (state : Vector ℕ 8) (k w : ℕ)` | | `Reference.round` (`Reference.lean:156`), on `Vars (BitVec 32)` |
| 69 | `messageSchedule : Vector ℕ 16 → Vector ℕ 64` | | `Reference.schedule` (`Reference.lean:129`) |
| 80 | `sha256Compress` (64 rounds, no feed-forward) | | inner fold of `Reference.compress` |
| 84 | `compressBlock` (with feed-forward) | `Vector ℕ 8 → Vector ℕ 16 → Vector ℕ 8` | `Reference.compress Hash.SHA2.sha256` (`Reference.lean:164`) |
| 90 / 94 | `bytesToWord32BE`, `bytesToBlock` | | `parse` / `Fast.loadBE` |
| 102 | `pad : List ℕ → List (Vector ℕ 16)` | bytes as `ℕ`, unchecked `< 256` | `Reference.pad` / `Fast.pad` |
| 116 | `sha256 : List ℕ → Vector ℕ 8` | | `Hash.sha256 : ByteArray → ByteArray` (`API.lean:30`) |
| `Clean/Specs/sha256.py` | Python oracle | | (n/a) |

### BLAKE3 (`Clean/Specs/BLAKE3.lean`, 368 lines)

| file:line | name | representation | counterpart |
|---|---|---|---|
| 44-50 | flag constants | ℕ | `Hash.BLAKE3.Flag.*` (`Reference.lean:46-58`) |
| 56 / 73 | `iv : Vector UInt32 8`, `msgPermutation : Vector (Fin 16) 16` | | `IV`, `msgPermutation` (`Reference.lean:35,39`) |
| 82 | `g (state : Vector ℕ 16) (a b c d : Fin 16) (mx my : ℕ)` | Nat words | inside `BLAKE2.Reference.round blake2sParams` |
| 117 / 126 | `round`, `permute` | | `Reference.round`, `Reference.permute` (`Reference.lean:79,82`) |
| 145 | `applyRounds cv m counter blockLen flags` | counter split as `% 2^32`, `/ 2^32` (unreduced) | the 7-round fold inside `Reference.compress` |
| 178 | `finalStateUpdate` | | the output step of `Reference.compress` |
| 203 | `compress (cv : Vector ℕ 8) (m : Vector ℕ 16) (counter blockLen flags : ℕ) : Vector ℕ 16` | | `Reference.compress (h m : List Word) (t b d : Nat)` (`Reference.lean:88`); `Fast.compress` (`Fast.lean:32`) |
| 216 | `ChunkState` (cv, counter, blocks_compressed, buffer) | **no flags field** | `Fast.State` (streaming) |
| 240 | `bytesToWords` | LE, zero-padded | `wordsLE` |
| 266 / 303 / 310 / 320 | `processBlockWords`, `processBlocksWords`, `updateChunk`, `finalizeChunk` | | `Reference.chunkOutput` (`Reference.lean:130`) |
| 329 | `processChunk cv counter bytes baseFlags : Vector ℕ 8` | | `(Reference.chunkOutput key flags i chunk).chainingValue`. **Agrees only when `baseFlags = 0` or the chunk has ≤ 64 bytes (§7.2).** |
| (none) | no parent nodes, root, XOF or tree | | `Hash.blake3`, `blake3Xof`, `blake3Keyed`, `blake3DeriveKey` |

### Poseidon (`Clean/Specs/Poseidon{,Optimized,Constants}.lean`)

| file:line | name | representation | counterpart |
|---|---|---|---|
| `Poseidon.lean:24,29` | `BN254_PRIME := BN254.scalarFieldSize`, `F := ZMod BN254_PRIME` | CompPoly prime, equal to our `Hash.ZK.bn254` (checked numerically) | `ZMod Hash.ZK.bn254` (`Primes.lean:29`) |
| `Poseidon.lean:36,38` | `N_ROUNDS_P`, `nRoundsP` | | `Circom.partialRounds` (`CircomParams.lean:42`): **identical list** |
| `Poseidon.lean:48-75` | `sigma`, `ark`, `mix` (`out_i = Σ_j M[j][i]·s_j`), `sboxFull`, `sboxPartial` | `Vector F t`, constants as `Vector ℕ` | `Reference.round` / `sboxLayer` (`Reference.lean:63-68`) |
| `Poseidon.lean:85-120` | `fullRoundCircom`, `partialRoundCircom`, `fullRoundsCircom`, `partialRoundsCircom` | circomlib order: initial ARK, then (SBOX → ARK → MIX); partial rounds with 1 constant and a dense `M` | `Reference.round` (ARC → SB → M, raw constants) |
| `Poseidon.lean:136,158,181,199` | `poseidon1` … `poseidon4` | t = 2..5 only | `Circom.poseidon n` (`Circom.lean:70`), t = 2..17 |
| `PoseidonConstants.lean:26,102,187,279` | `C_t2..C_t5` | **folded** constants, `8t + R_P` entries (72/81/88/100) | `Circom.params t`'s `C`, **raw**, `(8 + R_P)·t` entries (128/195/256/340), derived from Grain |
| `PoseidonConstants.lean:390-431` | `M_t2..M_t5` | stored **transposed** (`M_t[i][j] = our M j i`) | `Circom.params t`'s `M` (Cauchy) |
| `PoseidonConstants.lean:474-1581` | `P_t2..P_t4`, `S_t2..S_t4` | circomlib's pre-sparse and sparse matrices | **no counterpart** (§6) |
| `PoseidonOptimized.lean:33-162,216,292` | `mixS_t*`, `poseidon1Permutation`, `poseidon{1,2,3}Opt` | t = 2..4 | none (optimized form) |
| PR #465 `Specs/PoseidonParameterGeneration.lean` | Grain LFSR, `generateBase`, `compressConstants`, `sparseFactorize`, `reproduce` | executable generator, t = 2..17 | overlaps `Hash.ZK.Grain` (`Common/Grain.lean`) and `Circom.samples`/`fastParams` (`CircomParams.lean:59-69`) |
| PR #465 `Specs/PoseidonOptimized.lean:26,267,278` | generic `Params t`, `permutation`, `poseidon` | t = 2..17 (`params_t2..t17`) | none (optimized form) |

## 3. How it is used

Every hash spec in clean is the *target* of a correctness proof. The only executable uses are tests
and one export check. The table lists each spec site, at `def Spec` or its equivalent.

| Family | Proof targets (file:line → spec function) | Count |
|---|---|---|
| Keccak | `ThetaC.lean:28` → `thetaC`; `ThetaD.lean:41` → `thetaD`; `ThetaXor.lean:32` → `thetaXor`; `Theta.lean:27` → `theta`; `RhoPi.lean:30` → `rhoPi`; `Chi.lean:27` → `chi`; `KeccakRound.lean:28` → `keccakRound`; `Permutation.lean:21` → `keccakPermutation`; `AbsorbBlock.lean:39` → `absorbBlock`; `Tables/KeccakInductive.lean:23,53-55` → `absorbBlocks` (`tableStatement`) | 10 |
| Keccak (open PRs) | #489 `Examples/KeccakAir/*` (4 row gadgets, `table_block_soundness` → `keccakPermutation`); #492 `backends/compstark/CleanCompStark/KeccakShowcase.lean` (`keccak_soundness_ro`, via #489) | 2 |
| SHA-256 | `Ch32.lean:46`, `Maj32.lean:60`, `UpperSigma0.lean:39`, `UpperSigma1.lean:39`, `LowerSigma0.lean:39`, `LowerSigma1.lean:40`, `SHA256Round.lean:80` → `sha256Round`, `SHA256Schedule.lean:69` → `messageSchedule`, `SHA256Compress.lean:63` (`SHA256Rounds`) → `sha256Compress`, `SHA256Compress.lean:387` (`CompressBlock`) → `compressBlock` | 10 |
| BLAKE3 | `Permute.lean:22` → `permute`; `BLAKE3G.lean:74` → `g`; `Round.lean:46` → `round`; `ApplyRounds.lean:51-54,90-…,434` → `round`/`permute`/`applyRounds`; `FinalStateUpdate.lean:54` → `finalStateUpdate`; `Compress.lean:34` → `compress`; `FinalizeChunk.lean:117` → `finalizeChunk`; `Tables/BLAKE3/ProcessBlocksInductive.lean:196` → `processBlocksWords` | 8 |
| Poseidon | `Circomlib/Poseidon.lean:215` (`InitialArk`) → `ark`; `:240` (`FullRound_t2`) → `fullRoundOpt_t2`; `:285` (`ApplyFullRounds`) → `fullRoundsOpt_t2`; `:324` (`PartialRoundOpt_t2`) → `partialRoundOpt_t2`; `:395` (`ApplyPartialRoundsOpt`) → `partialRoundsOpt_t2`; `:450-451` (`Poseidon1`) → `poseidon1Opt`. **t = 2 only**; #465 generalises to 1..16 inputs. | 6 |

Executable uses, where a direct swap is possible:
- `native_decide` test vectors: `SHA256.lean` (42), `BLAKE3.lean` (4), `BLAKE3/ChunkProcessingTests.lean` (19),
  `Poseidon.lean` (7), `PoseidonOptimized.lean` (17). These could be checked against `Hash.*` instead.
  **Unverified:** whether clean accepts `native_decide`-free alternatives.
- `Examples/WitnessExport.lean:47` (`#assert_exportable` of `Keccak256.Permutation.circuit`).
- `Backends/Circom/TestWasmCompile.lean:221-274`: Poseidon1 compiled to WASM and checked
  against hard-coded ground truths.

**Conclusion.** No circuit should be re-targeted. Each family needs only a top-level bridge:
- Keccak: `keccakPermutation`, plus `absorbBlocks` after the fix in §7.1.
- SHA-256: `compressBlock` and `sha256`.
- BLAKE3: `compress` and `processChunk`.
- Poseidon: `poseidonNOpt`, or #465's `poseidon params`.

Every circuit theorem then transfers to the standard by composing with the bridge.

## 4. Representation gaps and adapter lemmas

| Gap | Adapter | Who provides |
|---|---|---|
| Keccak lane index `5x+y` vs `x+5y` | PR #489's `Lanes.toState : Lanes → Vector ℕ 25` (index `5x+y`) together with `CleanBridge.ofFast : Array UInt64 → Lanes`, `ofFast a x y = (Fast.lane a (x + 5y)).toBitVec`. Proved: `toRef (ofFast a) = Hash.Keccak.Equiv.toState a` by `rfl`. | clean: the transposition is clean-specific |
| Nat lanes ↔ BitVec / UInt64 | PR #489 has `toNat_rotateLeft : (l.rotateLeft o).toNat = rotLeft64 l.toNat o` and `toNat_not : (~~~l).toNat = not64 l.toNat`. Nothing more is needed if the bridge goes through `Lanes`. | clean (already written) |
| Keccak `Lanes` ↔ `Hash.Keccak.State 64` | `toRef L x y z = (L x y).getLsbD z`, `toRef_injective` (Appendix A) | **hash-specs could ship this generically**: `Hash.Keccak.ofLanes (L : Fin 5 → Fin 5 → BitVec 64) : State 64` with θ/ρ/π/χ/ι lemmas. This is useful to other repos too (VCVio, evm-asm). |
| Keccak block (`Vector ℕ 17`) ↔ bytes | `blockOfBytes (p : ByteArray) (off : Nat) : Vector ℕ 17 := .ofFn fun i => (p.getUInt64LE (off + 8*i)).toNat` | clean |
| SHA-256 Nat words ↔ `BitVec 32` | `add32 a.toNat b.toNat = (a + b).toNat` (`BitVec.toNat_add`); `rotRight32 x.toNat r = (x.rotateRight r).toNat` for `r < 32`; `x.toNat / 2^n = (x >>> n).toNat`; `not32 x.toNat = (~~~x).toNat` | clean (mirrors #489's 64-bit lemmas) |
| SHA-256 `Vector ℕ 8` ↔ `List (BitVec 32)` | `H.toList.map BitVec.toNat`; output words ↔ bytes: `natToBytesBE 4` / `Hash.SHA2.Fast.natToBytesBE` (`Fast.lean:94`) | clean |
| BLAKE3 Nat words ↔ `BitVec 32` | the same as SHA-256, plus `rotRight32 (x ^^^ y)` | clean |
| BLAKE3 counter | clean splits as `t % 2^32`, `t / 2^32` (unreduced). We use `BitVec.ofNat 32 (t / 2^32)`. They agree for `t < 2^64`, so the bridge needs `ht : t < 2^64`, `hb : b < 2^32`, `hd : d < 2^32`. | clean |
| Poseidon `ZMod BN254.scalarFieldSize` vs `ZMod Hash.ZK.bn254` | `BN254.scalarFieldSize = Hash.ZK.bn254` (same literal; the proof is expected to be `rfl` or `decide`, **unverified** because it needs CompPoly in scope) | clean |
| Poseidon matrix storage | `M_t[i][j] = (Circom.params t).M j i`: clean's `mix` reads `M[j][i]` (`Poseidon.lean:63`), so the linear maps agree | clean |
| Poseidon input vector | `Vector F n` vs `Fin n → ZMod bn254`: `fun i => xs[i]` | clean |

## 5. Bridge theorems

### 5.1 Keccak-f: proved (Appendix A)

Checked against hash-specs `98c225d` (v4.35.0). Verbatim copies of clean's `roundConstants` and
PR #489's `Lanes` definitions were used; 95 lines of proof.

```lean
-- in clean, e.g. Clean/Specs/Keccak256/HashSpecs.lean
theorem toRef_permutation (L : Specs.Keccak256.Lanes) :
    toRef (Lanes.permutation L) =
      (List.range 24).foldl (fun A (i : Nat) => Hash.Keccak.Rnd 6 A (i : Int)) (toRef L)

theorem permutation_ofFast (a : Array UInt64) :
    Lanes.permutation (ofFast a) = ofFast (Hash.Keccak.Fast.keccakF a)
```

The Nat-lane corollary, the form clean's circuits use, follows by composing with #489's
`Lanes.keccakPermutation_toState`:

```lean
theorem keccakPermutation_eq_keccakF (a : Array UInt64) :
    Specs.Keccak256.keccakPermutation (Lanes.toState (ofFast a)) =
      Lanes.toState (ofFast (Hash.Keccak.Fast.keccakF a)) := by
  rw [Lanes.keccakPermutation_toState, permutation_ofFast]
```

- **Difficulty:** structural. The proof mirrors `Hash.Keccak.Equiv.toState_*` step by step.
- The constant tables (`rotationOffsets` vs `ρOffset`, `roundConstants` vs `RC`) are discharged
  by `decide +kernel`.
- Corollary for the circuit: `Permutation.circuit`'s spec
  (`out.value = keccakPermutation state.value`) plus this theorem gives FIPS 202 Keccak-f[1600] on
  normalized states.

### 5.2 Keccak-256 sponge: blocked on §7.1, then medium

Once `absorbBlock` is fixed:

```lean
theorem absorbBlocks_keccak256 (m : ByteArray) :
    let p := Hash.Keccak.Fast.pad 136 0x01 m
    Specs.Keccak256.absorbBlocks ((List.range (p.size / 136)).map (blockOfBytes p <| 136 * ·)) =
      Lanes.toState (ofFast (Hash.Keccak.Fast.absorb 136 p))   -- `absorb` is a gap, §6
theorem keccak256_eq (m : ByteArray) :
    Hash.keccak256 m = (Hash.Keccak.Fast.rateBytes 136 (Hash.Keccak.Fast.absorb 136
      (Hash.Keccak.Fast.pad 136 0x01 m))).extract 0 32       -- hash-specs lemma, §6
```

The proof is an induction over blocks using `permutation_ofFast`, plus a per-lane XOR lemma.

### 5.3 SHA-256: medium (not attempted)

```lean
theorem Specs.SHA256.compressBlock_eq (H : Vector (BitVec 32) 8) (M : Vector (BitVec 32) 16) :
    (Specs.SHA256.compressBlock (H.map BitVec.toNat) (M.map BitVec.toNat)).toList =
      (Hash.SHA2.Reference.compress Hash.SHA2.sha256 H.toList M.toList).map BitVec.toNat

theorem Specs.SHA256.sha256_eq (m : ByteArray) :
    (Specs.SHA256.sha256 (m.data.toList.map UInt8.toNat)).toList.flatMap
        (fun w => [w / 2^24 % 256, w / 2^16 % 256, w / 2^8 % 256, w % 256]) =
      (Hash.sha256 m).data.toList.map UInt8.toNat
```

- **Difficulty: structural, medium.** Work for each of σ/Σ/Ch/Maj, plus two folds that differ in
  shape. clean uses `Fin.foldl` with `Vector.set` (`SHA256.lean:72-81`); we use `List.range`
  `foldl` over `List.getD` (`Reference.lean:129-171`).
- `K` and `H0` agreement is `decide`.
- `sha256_eq` additionally needs the bit-level padding/parse equivalence. Going through `sha256_eq`
  in `Hash/SHA2/Equiv.lean:335` (bits) is the shortest path. Alternatively, prove the Fast form by
  induction on blocks.

### 5.4 BLAKE3: medium (not attempted)

```lean
theorem Specs.BLAKE3.compress_eq (cv : Vector (BitVec 32) 8) (m : Vector (BitVec 32) 16)
    (t b d : ℕ) (ht : t < 2^64) (hb : b < 2^32) (hd : d < 2^32) :
    (Specs.BLAKE3.compress (cv.map BitVec.toNat) (m.map BitVec.toNat) t b d).toList =
      (Hash.BLAKE3.Reference.compress cv.toList m.toList t b d).map BitVec.toNat

theorem Specs.BLAKE3.processChunk_eq (key : Vector (BitVec 32) 8) (i : ℕ) (chunk : List UInt8)
    (hi : i < 2^64) (hc : chunk.length ≤ 1024) :
    (Specs.BLAKE3.processChunk (key.map BitVec.toNat) i (chunk.map UInt8.toNat) 0).toList =
      (Hash.BLAKE3.Reference.chunkOutput key.toList 0 i chunk).chainingValue.map BitVec.toNat
    -- general `flags` only after the fix in §7.2
```

- **Difficulty: medium.** clean's `g` uses explicit index tuples (`BLAKE3.lean:102-111`). Our
  `round` is BLAKE2s's (`BLAKE2.Reference.round blake2sParams m v 0`), so the proof must unfold
  through the BLAKE2 round schedule.
- `processChunk_eq` needs `splitIntoBlockWords` (well-founded recursion, `BLAKE3.lean:280-297`)
  related to our `chunkBlocks`/`chunks`.

### 5.5 Poseidon: hard

```lean
theorem Specs.Poseidon.poseidon1_eq (x : Specs.Poseidon.F) :
    Specs.Poseidon.poseidon1 x = Hash.ZK.Poseidon.Circom.poseidon 1 ![x]
theorem Specs.PoseidonOptimized.poseidon1Opt_eq (x : Specs.Poseidon.F) :
    Specs.PoseidonOptimized.poseidon1Opt x = Hash.ZK.Poseidon.Circom.poseidon 1 ![x]
-- after #465: for each t ∈ [2, 17]
theorem Specs.PoseidonOptimized.poseidon_eq (xs : Vector F (t - 1)) :
    Specs.PoseidonOptimized.poseidon params_t xs = Hash.ZK.Poseidon.Circom.poseidon (t - 1) (fun i => xs[i])
```

- **Hard.** clean's specs are both *optimized* forms.
  - `Poseidon.lean` places ARK after the S-box (C' = M⁻¹-shifted constants) and gives partial rounds
    one folded constant each.
  - `PoseidonOptimized.lean` additionally factors M into P and sparse S matrices.
- Neither is the textbook permutation, and clean's constants are tables, not derivations. So the
  bridge needs:
  1. a generic theorem that circomlib's transformation (constant compression + sparse
     factorisation) preserves the permutation;
  2. per-width identities between clean's tables and the transformation of our Grain-derived
     constants (decidable but heavy: up to 17×17 inverses over a 254-bit field).
- Today, `poseidon1Opt = poseidon1` is only tested at 4 points (`PoseidonOptimized.lean:340-343`),
  not proved.
- ROADMAP §1 says "the textbook and optimized versions are not proved equal". More precisely,
  *both* clean versions are optimized forms, and neither has been proved equal to the textbook
  permutation.

## 6. Gaps in hash-specs

| Gap | Needed for | Size |
|---|---|---|
| `Hash.Keccak.Fast.absorb (rate) (p : ByteArray) : Array UInt64` named and exposed, with `sponge_eq_absorb : sponge rate ds m d = (squeeze rate (absorb rate (pad rate ds m)) …).extract 0 d` and a `keccak256_eq` single-squeeze corollary | sponge bridge §5.2 | S |
| `Fast.size_keccakF : (keccakF a).size = 25` (and the same for `round`, `absorbBlock`); there are no size lemmas today | cleaner `Vector UInt64 25` statements | XS |
| A lane-function view `Fin 5 → Fin 5 → BitVec 64` (or `Vector UInt64 25`) of Keccak-f with `toState` lemmas: Appendix A's `toRef_*` generalised | clean, and any repo whose circuits index lanes as `(x, y)` | S |
| circomlib's **optimized** Poseidon (`C'`, `M`, `P`, `S`, derived from `Circom.params` by definition), with a generic equivalence theorem `optimized_eq_reference` | Poseidon bridge §5.5, and #465 | L (linear algebra over `Matrix (Fin t) (Fin t) F`) |
| The generator in #465 overlaps ours (`Hash.ZK.Grain`, `Circom.samples`). If clean consumed our derivation, its 1.5k-line constant tables and the #465 generator could go. | dedup | (n/a, maintainer decision) |
| SHA-256 at the compression level is fine (`Reference.compress`). `Fast.compress` takes bytes, not words (`Fast.lean:121`), so circuit-level bridges should target `Reference`. | (n/a) | (n/a) |

## 7. Discrepancies

Scratch files are in
`evidence/clean/`:
`CleanCopy.lean`, `ShaBlake.lean` and `KeccakBridge.lean`. Each contains verbatim copies of clean's
defs and was run with `lake env lean` in hash-specs.

### 7.1 Keccak `absorbBlock` uses the wrong lanes (bug in clean)

- clean indexes lane `(x, y)` at `5x + y`. This is proved by the code: `thetaC` sums
  `state[5x..5x+4]` (`Keccak256.lean:28-32`), and `chi` uses `b[i+5]`, `b[i+10]` for `x+1`, `x+2`
  (l.109). Check (A): `keccakPermutation` is Keccak-f[1600] under the `5x+y ↔ x+5y` transposition
  (`CleanCopy.lean`, `KCheck`: `true` on random and zero states). Appendix A proves it.
- `absorbBlock` XORs `block[i]` into `state[i]` for `i < 17` (`Keccak256.lean:156`). The
  `AbsorbBlock` circuit does the same (`AbsorbBlock.lean:20-25`).
- Those indices are lanes `(x, y) = (i/5, i%5)`. In FIPS order they are
  `{0,5,10,15,20,1,6,11,16,21,2,7,12,17,22,3,8}`, which includes **capacity lanes 17, 20, 21 and
  22**. So no encoding of the message into `block` makes `absorbBlocks` the Keccak[c=512] absorb.
- Check (B), on the empty message (block `[1, 0, …, 0, 2^63]`, digest read from lanes `(0..3, 0)`):

  | Variant | Digest |
  |---|---|
  | clean `absorbBlocks` | `0eab42de4c3ceb9235fc91acffe746b29c29a8c366b7c60e4e67c466f36a4304` |
  | transposed absorb | `c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470` |
  | `Hash.keccak256 ∅` | `c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470` |

- clean's own Python oracle does it right: `state_absorb_block` writes `new_state[x*5 + y]`
  (`Clean/Specs/keccak.py:202`), and `state_squeeze` reads in the same order (l.212). The Lean port
  dropped the transposition.
- **Impact.** `Tables.KeccakInductive.tableStatement` (`KeccakInductive.lean:52-55`) says the
  output "is the result of keccak-hashing some list of input blocks". What it proves is a
  different, non-standard sponge. The permutation circuits are unaffected.
- **Fix:** XOR `block[i]` into `state[5*(i%5) + i/5]` in both the spec and the circuit.

### 7.2 BLAKE3 `processChunk` drops the mode flags on non-final blocks (bug or limitation in clean)

- `processBlockWords` compresses with `flags := startFlag state` (`BLAKE3.lean:267`). `ChunkState`
  has no flags field (l.216-220). Only `finalizeChunk` ORs in `base_flags` (l.322).
- BLAKE3 sets the mode flags (`KEYED_HASH`, `DERIVE_KEY_*`) on *every* block of a chunk. Ours does
  (`Reference.lean:130-137`).
- Check (`ShaBlake.lean`): `processChunk iv 0 bytes fl` vs
  `(Fast.chunkOutput ivWords fl 0 bytes).chainingValue`:

  | Inputs | Result |
  |---|---|
  | `fl ∈ {16, 64}`, lengths 0, 1, 64 | agree |
  | `fl ∈ {16, 64}`, lengths 65, 129, 1024 | **disagree** |
  | `fl = 0` (lengths 0..1024, counter 0 and 5) | agree |

- clean's only keyed-mode test uses 1 byte (`ChunkProcessingTests.lean:119-124`), so it cannot
  catch this.
- `Tables/BLAKE3/ProcessBlocksInductive.lean` is proved against `processBlocksWords` and inherits
  the limitation. Plain `blake3` hashing (flags 0) is unaffected.

### 7.3 Agreements (no discrepancy)

| Family | What I compared | Result |
|---|---|---|
| SHA-256 | `Specs.SHA256.sha256` vs `Hash.sha256` on lengths 0, 1, 3, 55, 56, 63, 64, 65, 119, 120, 200, 1000 (padding boundaries) | all equal |
| BLAKE3 | `Specs.BLAKE3.compress` vs `Hash.BLAKE3.Fast.compress`, 5 random `(cv, m, t < 2^64, b, d)` | all equal |
| Poseidon output | `poseidon1..4` vs our `Circom.poseidon` (through `Fast.permutation (fastParams …)`) on 12 inputs, including all of clean's vendored circomlibjs vectors; our `poseidon([1,2]) = 0x115cc0f5…189a` | all equal |
| Poseidon parameters | `N_ROUNDS_P` vs `partialRounds` | identical |
| | `M_t2..M_t5` | equal to ours *transposed*, consistent with `mix` |
| | `C_t*[0..t-1]` | equal to our round-0 constants |
| | `C_t*` from index `t` on | differ (folded constants, as expected) |

**Nat-domain caveats** (not bugs):
- `rotRight64`/`rotRight32` (`Bitwise.lean:25-35`) do not truncate inputs ≥ `2^w`.
- `SHA256.pad` and `BLAKE3.bytesToWords` accept list elements ≥ 256.

The circuits supply the bounds through `Normalized`, so every bridge must carry `< 2^w` or come
from `BitVec`/`UInt8` (as in §5).

## 8. PR plan

Conventions:
- PR titles are mixed: `feat(scope): …`, `chore: …`, `fix(…): …`, or plain sentences (#466,
  #460, #457, #462).
- CI runs `lake build --wfail` and `lake build CleanTests`.
- There is no CONTRIBUTING and no CODEOWNERS. `mitschabaude` reviews.
- There is no explicit AI-disclosure rule, but recent PRs and issues state it (e.g. #396
  "written by Claude Code"). Do the same.
- Open PRs touching these files:
  - #487: toolchain. It touches `Circomlib/Poseidon.lean`, `SHA256Compress.lean`,
    `SHA256Schedule.lean` and `ProcessBlocksInductive.lean`.
  - #465: Poseidon, n-arity. Open since 2026-09-17, REVIEW_REQUIRED.
  - #489 and #492: keccak-air. Drafts that build on `Specs.Keccak256`.

**Prerequisites in hash-specs (do first):**

- **H1. `feat(keccak): expose the sponge absorb and lane-function view`**
  - Files: `Hash/Keccak/Fast.lean`, `Equiv.lean`, `README.md`.
  - Adds `Fast.absorb`, `sponge_eq_absorb`, `keccak256_eq_absorb`, and `size_keccakF`/`size_round`.
  - Optionally adds a `Lanes` view with Appendix A's `toRef_*` lemmas, stated generically.
  - Size: S, about 150 lines. Risk: none (additive).
- **H2 (later). `feat(poseidon): circomlib's optimized permutation and its equivalence`**
  - Files: `Hash/ZK/Poseidon/Optimized.lean`.
  - Adds the folded constants `C'`, the `P` and `S` matrices derived from `Circom.params`, and
    `optimized_eq_reference`.
  - Size: L. Risk: proof effort. Do it only if the clean maintainers want the Poseidon bridge.

**PRs to clean, in order:**

1. **`fix(keccak): absorb block lanes in FIPS 202 order`** (independent of hash-specs; do it now)
   - Files: `Clean/Specs/Keccak256.lean` (`absorbBlock`), `Clean/Gadgets/Keccak/AbsorbBlock.lean`
     (`main`, plus the soundness and completeness case split on `i < 17`, l.41-109).
   - Adds a regression `example` with the empty-message digest.
   - Proofs to rework: `AbsorbBlock.soundness/completeness`. `KeccakInductive` keeps its statement
     unchanged.
   - Size: S–M, about 100 lines changed.
   - Risk: the witness layout changes, so check `WitnessExport` and the Plonky3 artifacts. Draft
     #491 and #492 may assume the current layout (**unverified**).
2. **`fix(blake3): carry the mode flags into every block of a chunk`**, or alternatively
   **`docs(blake3): processChunk supports flags = 0 only`**
   - Files: `Clean/Specs/BLAKE3.lean` (add a `flags` field to `ChunkState`, use it in
     `processBlockWords`), `Clean/Tables/BLAKE3/ProcessBlocksInductive.lean` (the state gains a
     flags column), `FinalizeChunk.lean`.
   - Size: M. Risk: changes the table layout. This is a maintainer decision (§9).
3. **`chore: depend on hash-specs`**: only after #487 merges.
   - `lakefile.lean`: add, after the Mathlib require,
     ```lean
     require «hash-specs» from git "https://github.com/Verified-zkEVM/hash-specs" @ "v4.35.0-patch1"
     ```
     then `lake update hash-specs`.
   - No code changes. Nothing deleted.
   - Size: XS. hash-specs sets `preferReleaseBuild`, so oleans are fetched and CI time barely moves
     (**unverified** on clean's runners).
   - Risk: the transitive pins must resolve to the same Mathlib `56a0058`. They do as of #487.
4. **`feat(keccak): prove Keccak-f equal to hash-specs`**
   - Adds `Clean/Specs/Keccak256/HashSpecs.lean` with Appendix A and the Nat-lane corollary §5.1.
   - Depends on #489's `Keccak256BitVec.lean`. If #489 has not merged, include that file or rebase
     onto it.
   - Then add `absorbBlocks_keccak256` (§5.2) once PR 1 and H1 have landed.
   - Size: S (permutation) + M (sponge). Risk: low. Nothing is deleted.
5. **`feat(sha256): prove the SHA-256 spec equal to hash-specs`**
   - Adds `Clean/Specs/SHA256/HashSpecs.lean`: `compressBlock_eq`, `sha256_eq`, and the 32-bit
     adapter lemmas.
   - Optionally, re-check the `native_decide` vectors against `Hash.sha256`.
   - Size: M (about 300 lines). Risk: the `Fin.foldl` vs `List.foldl` shapes. On 4.33 the
     schedule fold had to be made `irreducible` (`SHA256Compress.lean:361-363`).
6. **`feat(blake3): prove BLAKE3 compress and processChunk equal to hash-specs`**
   - Adds `Clean/Specs/BLAKE3/HashSpecs.lean`. `processChunk_eq` covers `flags = 0`, or general
     flags after PR 2.
   - Size: M. Risk: `splitIntoBlockWords` uses well-founded recursion.
7. **`feat(poseidon): prove the optimized circomlib Poseidon equal to hash-specs`**
   - Wait for #465 and H2. Then `PoseidonOptimized.poseidon_eq` for t = 2..17.
   - Optionally replace `PoseidonConstants.lean` (1,581 lines) and #465's generator with our
     derivation.
   - Size: M–L. Risk: kernel cost of the per-width constant identities.
8. **(later) `refactor: drop duplicated executable hash code`**
   - Candidates: `Specs/SHA256.lean:90-117` (`bytesToWord32BE`, `bytesToBlock`, `pad`, `sha256`),
     used only by tests, and the BLAKE3 test helpers. Tests would move to `Hash.*`.
   - Keep the circuit-facing step functions: every gadget spec cites them.
   - Size: S. Make this optional; it changes nothing proved.

## 9. Open questions for the maintainers

1. **Keccak absorb (§7.1).** Was the non-transposed absorb intentional, for example a simplified
   "sponge-like" demo? If so, should the spec and `tableStatement` be renamed so that they do not
   claim Keccak-256? If not, is PR 1 welcome before the keccak-air stack (#489–#492) lands?
2. **BLAKE3 flags (§7.2).** Should `processChunk` support keyed and derive-key modes, which means
   a flags field in `ChunkState` and the table? Or should it be documented as plain-hash only?
3. **Toolchain.** When will #487 merge, and will CompPoly stay on the `mitschabaude-bot` fork?
   This does not matter for core `hash-specs`, but it would if clean ever wanted `hash-specs-zk`.
4. **#489's `Lanes`.** Is it the intended long-term BitVec view? If so, should hash-specs provide
   it (H1), with clean importing it rather than defining its own?
5. **Poseidon.** Is a proved bridge from the optimized circuits to the textbook permutation
   wanted (H2 + PR 7)? And would clean accept constants derived in hash-specs in place of its
   tables and #465's generator?
6. **Where should bridges live:** next to each spec (`Clean/Specs/*/HashSpecs.lean`), or in a
   separate `CleanHashSpecs` lib so that the core `Clean` lib does not depend on hash-specs?
7. **`native_decide`.** clean uses it for 89 test vectors. Is it acceptable in bridge proofs? The
   proofs above use only `decide +kernel`.

## Appendix A: Keccak-f bridge (proved, hash-specs `98c225d`, Lean v4.35.0)

Preceded in the scratch file by verbatim copies of clean's `Specs.Keccak256.roundConstants`
(`Keccak256.lean:8-21`) and of #489's `Specs.Keccak256.rotationOffsets` and `Lanes.*`
(`Keccak256BitVec.lean:16-71` at `253b952`).

`#print axioms CleanBridge.permutation_ofFast` gives `[propext, Classical.choice, Quot.sound]`.
There are no warnings.

```lean
namespace CleanBridge
open Specs.Keccak256 Hash.Keccak

/-- The bit-level state of a `Lanes` state: `A[x][y][z]` is bit `z` of lane `(x, y)`. -/
def toRef (L : Lanes) : State 64 := fun x y z => (L x y).getLsbD z.val

theorem toRef_injective {L L' : Lanes} (h : toRef L = toRef L') : L = L' := by
  funext x y
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact congrFun (congrFun (congrFun h x) y) ⟨i, hi⟩

theorem toRef_theta (L : Lanes) : toRef (Lanes.theta L) = θ (toRef L) := by
  funext x y z
  have hz := z.isLt
  have hx4 : x + 4 = x - 1 := by revert x; decide
  have hzs : (zsub z 1).val = (z.val + 63) % 64 := by simp [zsub]
  simp only [toRef, Lanes.theta, Lanes.columnParity, θ, D, C, hx4, BitVec.getLsbD_xor,
    BitVec.getLsbD_rotateLeft, hzs]
  rcases Nat.eq_zero_or_pos z.val with h0 | h0
  · simp [h0]
  · have : (z.val + 63) % 64 = z.val - 1 := by omega
    simp [this, show ¬ z.val < 1 by omega, hz]

theorem rotationOffsets_eq (a b : Fin 5) :
    (rotationOffsets[a][b] : Nat) = ρOffset a b % 64 := by
  revert a b
  decide +kernel

theorem toRef_rhoPi (L : Lanes) : toRef (Lanes.rhoPi L) = π (ρ (toRef L)) := by
  funext x y z
  have hz := z.isLt
  simp only [toRef, Lanes.rhoPi, π, ρ, zsub, BitVec.getLsbD_rotateLeft]
  rw [show ((rotationOffsets[x + 3 * y][x] : Fin 64) : Nat) % 64 = ρOffset (x + 3 * y) x % 64 by
    rw [rotationOffsets_eq, Nat.mod_mod]]
  generalize ρOffset (x + 3 * y) x = n
  by_cases h : z.val < n % 64
  · simp [h, show (z.val + (64 - n % 64)) % 64 = 64 - n % 64 + z.val by omega]
  · simp [h, hz, show (z.val + (64 - n % 64)) % 64 = z.val - n % 64 by omega]

theorem toRef_chi (L : Lanes) : toRef (Lanes.chi L) = χ (toRef L) := by
  funext x y z
  have hz := z.isLt
  simp [toRef, Lanes.chi, χ, hz]

theorem roundConstants_getLsbD (i : Fin 24) (z : Fin 64) :
    (Specs.Keccak256.roundConstants[i]).toBitVec.getLsbD z.val = RC 6 i.val z.val := by
  revert i z
  decide +kernel

theorem toRef_iota (L : Lanes) (i : Fin 24) :
    toRef (Lanes.iota L (Specs.Keccak256.roundConstants[i]).toBitVec) = ι 6 (toRef L) i.val := by
  funext x y z
  simp only [toRef, Lanes.iota, ι]
  by_cases h : x = 0 ∧ y = 0
  · simp only [h, and_self, ↓reduceIte, BitVec.getLsbD_xor]
    rw [roundConstants_getLsbD i z]
  · simp [h]

theorem toRef_round (L : Lanes) (i : Fin 24) :
    toRef (Lanes.round L Specs.Keccak256.roundConstants[i]) = Rnd 6 (toRef L) i.val := by
  simp only [Lanes.round, Rnd, toRef_iota, toRef_chi, toRef_rhoPi, toRef_theta]

/-- clean's `Lanes.permutation` is FIPS 202 Keccak-p[1600, 24], round by round. -/
theorem toRef_permutation (L : Lanes) :
    toRef (Lanes.permutation L) =
      (List.range 24).foldl (fun A (i : Nat) => Rnd 6 A (i : Int)) (toRef L) := by
  have hrc : Specs.Keccak256.roundConstants.toList =
      (List.finRange 24).map fun i => Specs.Keccak256.roundConstants[i] := by
    decide +kernel
  simp only [Lanes.permutation, ← Vector.foldl_toList, hrc, List.foldl_map]
  rw [show List.range 24 = (List.finRange 24).map Fin.val by decide]
  rw [List.foldl_map]
  generalize List.finRange 24 = l
  induction l generalizing L with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, ← toRef_round, ih]

/-- The lanes of a hash-specs state (lane `(x, y)` at index `x + 5y`). -/
def ofFast (a : Array UInt64) : Lanes := fun x y => (Fast.lane a (x.val + 5 * y.val)).toBitVec

theorem toRef_ofFast (a : Array UInt64) : toRef (ofFast a) = Equiv.toState a := rfl

/-- **Bridge.** clean's Keccak-f (PR #489's `Lanes.permutation`) agrees with hash-specs'
`Hash.Keccak.Fast.keccakF` on every state. -/
theorem permutation_ofFast (a : Array UInt64) :
    Lanes.permutation (ofFast a) = ofFast (Fast.keccakF a) := by
  apply toRef_injective
  rw [toRef_permutation, toRef_ofFast, toRef_ofFast, Equiv.toState_keccakF]
  congr 1
  funext A i
  congr 1
  omega

end CleanBridge
```

Porting note: inside clean, `open Specs.Keccak256 Hash.Keccak` makes `roundConstants`, `theta`,
`chi`, … ambiguous between the two namespaces. That is why the proof writes
`Specs.Keccak256.roundConstants` in full.
