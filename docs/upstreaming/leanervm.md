# Upstreaming record: `leanerVM`

Prepared 2026-10-27 against hash-specs `98c225d`. Every claim about leanerVM cites a file and line at the commit below. Paths without a repository prefix are in leanerVM. Anything not checked is marked **unverified**.

## 1. Snapshot

| | |
|---|---|
| Repo | `Verified-zkEVM/leanerVM` |
| Commit | `a37b2b0` (`a37b2b045b6e6c8e70697c5332ae04683b157b55`), 2026-10-22 |
| Date examined | 2026-10-27 |
| Toolchain | `leanprover/lean4:v4.34.1` (`lean-toolchain`) |
| Mathlib | `v4.34.1` = `d13f23b7` (`lakefile.toml`, `upstreams.json`) |
| CompPoly | `572f997` (main, not a release tag) |
| Clean | `42fe4b26`, a compatibility commit from Clean PR #474 (`docs/dependencies.md`) |
| ArkLib / VCVio / PolyFun | `7653a90` / `a4232d0` (from VCVio #820) / `41d3b21` |
| leanVM (the Rust target, not a Lake dependency) | `leanEthereum/leanVM@a386121f` (`upstreams.json`, `docs/dependencies.md`) |
| Lakefile | `lakefile.toml`. `warningAsError = true`, `autoImplicit = false`. The test library `LeanerVMTests` has `allowNonModules = true`. |
| Module system | Yes, in all production files (for example `LeanerVM/Semantics/Blake2s.lean:8`, `CONTRIBUTING.md` "Lean files and modules"). Tests may be classic files. |

**Toolchain gap.** leanerVM is on v4.34.1. hash-specs is on v4.35.0, and its releases are `v4.34.0`, `v4.35.0` and `v4.35.0-patch1` (`gh release list`). No release matches v4.34.1, so adopting hash-specs means either a new hash-specs release or a leanerVM toolchain bump.

- **Option A (recommended): cut a hash-specs `v4.34.1` release.**
  - Branch from tag `v4.34.0`. The BLAKE2 API is the same there as at HEAD; I checked `git show v4.34.0:Hash/BLAKE2/API.lean`.
  - Set `lean-toolchain` and the Mathlib requirement to `v4.34.1`.
  - Leave out `preferReleaseBuild`, or cherry-pick `98c225d` so the release carries prebuilt oleans.
  - The core package requires only Mathlib, so CompPoly does not constrain it. The `zk` package has to agree on toolchain (`scripts/check_layers.py`). Its CompPoly would then be built from source, as ROADMAP §2.1 records for the earlier v4.34.1 attempt ("It works, but CompPoly then has to be built from source").
  - Effort: small.
- **Option B: leanerVM bumps to v4.35.0.**
  - CompPoly, ArkLib, VCVio and PolyFun have HEADs on v4.35.0 (from the local clones, 2026-10-26/27).
  - Clean `main` is still on v4.33.1 (clean `0d76409`). leanerVM already depends on a Clean compatibility commit for 4.34, so a 4.35 bump needs another Clean compatibility branch.
  - The bump process in `docs/dependencies.md` is heavy: drift review, a full import-cone build, and an API review.
  - Effort: medium to hard, and not ours to schedule.

No pending toolchain bump is open: none of the 51 open PRs changes `lean-toolchain`. **Unverified**: I only checked titles and the Blake2s-related file lists, not every PR's files.

## 2. Overlap inventory

leanerVM has **no Poseidon, Keccak or SHA-2** on `main`. leanVM's current design replaced the KoalaBear field and Poseidon with the binary tower `K = GF(2^64)`, `E = GF(2^192)` and BLAKE2s:

- `README.md:6`: the KoalaBear/Poseidon version is kept on the `koalabear` branch.
- `docs/leanvm-target.md:31-40`: the "Hash relation" row reads "Poseidon" for the old design and "BLAKE2s compression" for the current one.

A grep for poseidon/keccak/sha256/koalabear/babybear in `*.lean` finds only `LeanerVM/Protocol/Field.lean:27`, a comment naming `KoalaBear.Ext6.sampleableType`. So the only overlap is with core `Hash.BLAKE2`; `hash-specs-zk` is not needed.

| leanerVM definition (file:line) | Signature / representation | hash-specs replacement |
|---|---|---|
| `LeanerVM.Parameters.iv` `Parameters/Blake2s.lean:31` | `Vector UInt32 8` | `Hash.BLAKE2.blake2sParams.IV : List Nat` (`Hash/BLAKE2/Reference.lean:172`); `Hash.BLAKE2.blake2s_IV` (`Constants.lean:27`) |
| `LeanerVM.Parameters.sigma` `Parameters/Blake2s.lean:37` | `Vector (Vector (Fin 16) 16) 10` | `Hash.BLAKE2.SIGMA : List (List Nat)` (`Reference.lean:53`); `SIGMA_perm` |
| `Semantics.Blake2s.rotr` `Semantics/Blake2s.lean:65` | `UInt32 → ℕ → UInt32`, `x.toBitVec.rotateRight n` | `BitVec.rotateRight` in `Reference.G`; `Fast.Word.rotr` (`UInt32.rotr`) |
| `Semantics.Blake2s.mix` `:68` | `Vector UInt32 16 → (a b c d : Fin 16) → (x y : UInt32) → Vector UInt32 16`, four writes at the end | `Reference.G blake2sParams` over `List (BitVec 32)` with `Nat` indices, written in sequence (`Reference.lean:78`); `Fast.G` (`Fast.lean:72`) |
| `Semantics.Blake2s.round` `:81` | `(v m : Vector UInt32 16) (s : Vector (Fin 16) 16)`; takes the schedule *row* | `Reference.round P m v i` (`Reference.lean:92`); takes the *round index* and looks up `SIGMA[i % 10]`. The argument order is `m v`. |
| `Semantics.Blake2s.initialState` `:93` | `h t (f0 f1 : UInt32)`. XORs `f0` into `v[14]` and `f1` into `v[15]`. | Inlined in `Reference.F`, with only `f : Bool` complementing `v[14]`. **No `f1` (last node).** |
| `Semantics.compress` `:105` | `Vector UInt32 8 → Vector UInt32 16 → UInt64 → UInt32 → UInt32 → Vector UInt32 8` | `Reference.F blake2sParams 10 h m t.toNat f` (`Reference.lean:108`), or `Fast.F` (`Fast.lean:97`). This covers only `f0 ∈ {0, 0xFFFFFFFF}`, `f1 = 0`; the general case has **no counterpart** (§6). |
| `lowWord`, `highWord`, `ofWords`, `cellWords`, `wordsCell`, `unpackMetadata`, `messageWords` `:115-142` | leanVM cell encoding over `K`, `E` | no counterpart (VM-specific, keep) |
| `CompressCells` `:148` | `Prop` on nine `E` cells | no counterpart (VM relation, keep) |
| `Protocol.Digest` `Protocol/Blake2sHash.lean:41` | `Vector UInt32 8` | the 32-byte `ByteArray` from `Hash.blake2s` |
| `Blake2sHash.lastBlock` `:53`, `paramIv` `:58` | `UInt32`; `iv` with `0x01010020` XORed into word 0 | computed inside `Reference.hash` (`Reference.lean:140-146`) from `paramBlock` (`:120`) and inside `Fast.hashWith` (`Fast.lean:125`); no standalone definition |
| `leWord` `:61`, `blockWords` `:66` | four bytes to a `UInt32`; a block of `List UInt8` to `Vector UInt32 16` | `Reference.wordsLE` (`Reference.lean:70`), `Fast.block`, `ByteArray.getUInt32LE` |
| `absorb` `:76` | `Vector UInt32 8 → ℕ → (blocks : ℕ) → List UInt8 → Digest` | the block loop in `Reference.hash`, `Fast.hashWith`; streaming `Hash.blake2sInit` |
| `blake2sBytes` `:84` | `List UInt8 → Vector UInt32 8` | **`Hash.blake2s : ByteArray → ByteArray`** (`API.lean:36`); `Reference.hash blake2sParams [] [] [] 32` (via `Hash.BLAKE2.blake2s_eq`, `Equiv.lean:408`) |
| `wordBytes` `:90`, `digestBytes` `:94` | LE bytes of a word or digest, as `List UInt8` | `Reference.bytesLE` (`Reference.lean:74`) |
| `kBytes` `:97`, `hashWords` `:102`, `hashPair` `:106` | leanVM's Merkle leaf and node hashes (`merkle.rs`) | none needed; they keep composing over `blake2sBytes` |
| `digestScalars` `:113`, `digestOfScalars` `:118` | digest as two `E` cells | no counterpart (VM encoding) |
| `leafImage`, `merkleRoot`, `merklePath`, `merkleVerify`, `merkleCollision` `Protocol/Merkle.lean:46-89` | generic Merkle tree over `hashWords`/`hashPair` (`MerkleTree.*` from `Protocol/ToArkLib/Merkle.lean`) | no counterpart (hash-specs has no Merkle trees); they do not depend on BLAKE2s internals |
| `Blake2sCircuit.gW/roundW/initW/compressW` `Protocol/Blake2sCircuit.lean:94-127` | R1CS gadgets mirroring `mix/round/initialState/compress` | no counterpart (circuit) |
| `Blake2sRelation` `Arithmetization/Tables/Blake2s.lean:146` | `CompressCells` on a table row | no counterpart |

Open stack PRs add more overlap. PR #119, "[06/43] perf(protocol): field arithmetic and BLAKE2s through proved fast paths", adds:

- `LeanerVM/Semantics/Blake2sFast.lean`: `compressFast`, `mixFast_eq`, `roundFast_eq`, and `rotr16`/`rotr12`/`rotr8`/`rotr7` as shift pairs;
- `LeanerVM/Protocol/Blake2sHashFast.lean`: `blake2sBytesFast`, `absorbFast_eq`, `blockWordsFast_eq`.

This is a second fast layer proved equal to the reference, which duplicates `Hash.BLAKE2.Fast` plus `Equiv`. PR #125 ("[12/43] the Fiat–Shamir chain") makes `blake2sBytes` the deployed random oracle of the transcript (`fsSeed`, `observe`, `sample`, `grind`, `checkPow` in `LeanerVM/Protocol/Transcript.lean`, from `gh pr diff 125`).

## 3. How it is used

**Specs that are the target of a correctness proof.** Re-targeting these goes through a bridge; re-proving them is not recommended.

| Target | Consumers |
|---|---|
| `compress` | `Blake2sCircuit.blake2s_sound` (`Blake2sCircuit.lean:530`), `blake2s_sound_words` (`:554`), `blake2s_complete` (`:597`), and the private `sound_compressW` (`:303`) and `compress_getElem` (`:292`, proved by `fin_cases k <;> rfl`, so it **unfolds `compress`**). `FlockSpec.compress_of_holds` (`FlockSpec.lean:247`) applies `blake2s_sound` at `:255` and then `unfold LimbsCompress CompressCells`; `limbsCompress_unique` (`FlockSpec.lean:328`) unfolds `CompressCells`. |
| `CompressCells` | `Semantics/Step.lean:151` (the `.blake2s` arm of `executeWith`: `guard (CompressCells …)`); `FlockSpec.LimbsCompress` (`FlockSpec.lean:72`); `Blake2sRelation` (`Tables/Blake2s.lean:146`), the table's named assumption, which Flock discharges. All of these quantify over **arbitrary** flag words. |
| `hashWords`, `hashPair` | `Merkle.lean`. The binding theorem `collision_of_merkleVerify` (`:82`) treats both as abstract functions, so nothing depends on BLAKE2s itself. In the stack, the ROM proofs (#127 "the hash oracle", #144 "the hash misbehaves") treat the hash as an oracle too. |

**Executable uses**, where a direct swap is possible:

- `blake2sBytes` in `Protocol/Blake2sHash.lean` (5 occurrences) and in the stack's `Transcript.lean`.
- Tests:
  - `tests/LeanerVMTests/Protocol/Blake2sHash.lean`: `blake2sBytes` 8 times; hashlib vectors for lengths 0, 3, 64, 65 and 128, plus `hashPair` and `hashWords`.
  - `tests/LeanerVMTests/Semantics/Blake2s.lean`: `compress` 6 times and `CompressCells` 11 times; RFC 7693 App. B; hashlib vectors with and without `last_node`; Rust executor vectors.
  - `tests/LeanerVMTests/Protocol/Merkle.lean`.

**Call-site counts** (`grep -rn --include='*.lean'`, by file):

| Name | Production | Tests |
|---|---|---|
| `compress ` | Semantics/Blake2s 4, Blake2sCircuit 5, Blake2sHash 2, and 2 doc mentions (Statement, Spine/Instance) | 9 |
| `CompressCells` | Semantics/Blake2s 6, Tables/Blake2s 5, FlockSpec 5, Step 3 | 17 |
| `blake2sBytes` | Blake2sHash 5 | 8 |
| `hashWords` | 9 | 7 |
| `hashPair` | 9, plus 34 in `ToArkLib/Merkle.lean` as a bound variable name | 4 |

Nothing has to change for the bridge-only plan. Swapping in a hash-specs definition would touch the `blake2sBytes` definition and its stack consumers only.

## 4. Representation gaps and adapter lemmas

| leanerVM | hash-specs | Adapter |
|---|---|---|
| `Vector UInt32 n` | `List (BitVec 32)` (Reference), `Array UInt32` (Fast) | `v.toList.map UInt32.toBitVec`; `UInt32.toBitVec` is `LawfulWord.toBV` (`Equiv.lean:50`) |
| `Fin 16` schedule rows | `List (List Nat)` and round index | `sigma.toList.map (·.toList.map Fin.val) = Hash.BLAKE2.SIGMA`, by `decide` |
| `t : UInt64`, `(t >>> 32).toUInt32` | `t : Nat`, `BitVec.ofNat 32 (t / 2^32)` | `t.toNat` (exact, since `t < 2^64`) |
| flag word `0xFFFFFFFF` XORed in | `f : Bool`, `~~~v[14]` | `x ^^^ 0xFFFFFFFF = ~~~x` (`BitVec.xor_allOnes`-style) |
| `List UInt8` | `ByteArray` | `⟨data.toArray⟩`, `.data.toList` |
| `Digest = Vector UInt32 8` | 32-byte `ByteArray` | `digestBytes` |

Lemmas, with where each belongs:

```lean
-- leanerVM (VM-specific shapes: Vector, Fin schedule)
theorem iv_toNat : iv.toList.map UInt32.toNat = Hash.BLAKE2.blake2sParams.IV := by decide
theorem sigma_val : sigma.toList.map (fun s => s.toList.map Fin.val) = Hash.BLAKE2.SIGMA := by decide
theorem mix_toBitVec (v : Vector UInt32 16) (a b c d : Fin 16) (x y : UInt32)
    (h : [a, b, c, d].Nodup) :
    (Blake2s.mix v a b c d x y).toList.map UInt32.toBitVec =
      Hash.BLAKE2.Reference.G Hash.BLAKE2.blake2sParams (v.toList.map UInt32.toBitVec)
        a b c d x.toBitVec y.toBitVec
theorem round_toBitVec (v m : Vector UInt32 16) (i : Fin 10) :
    (Blake2s.round v m sigma[i]).toList.map UInt32.toBitVec =
      Hash.BLAKE2.Reference.round Hash.BLAKE2.blake2sParams (m.toList.map UInt32.toBitVec)
        (v.toList.map UInt32.toBitVec) i
theorem digestBytes_eq (d : Digest) :
    digestBytes d = (d.toList.map UInt32.toBitVec).flatMap
      (Hash.BLAKE2.Reference.bytesLE Hash.BLAKE2.blake2sParams)
```

`mix` needs distinct indices. `Reference.G` writes in sequence and reads back, while `mix` binds locals and writes at the end; they agree when `a b c d` are pairwise distinct, which holds for all eight index tuples.

hash-specs should provide the generic ones: `Reference.F_length : (Reference.F P r h m t f).length = 8` and `Fast.F_size` (neither exists today; `grep` of `Hash/BLAKE2/*.lean`), so that downstream code can rebuild a `Vector` from the result. It should also provide a two-flag compression (§6).

## 5. Proposed bridge theorems

All of these live in leanerVM. Names on our side are checked against `Hash/BLAKE2/{Reference,API,Equiv}.lean` at `98c225d`.

```lean
/-- The opcode's compression at a Boolean last-block flag and no last-node flag is RFC 7693's F. -/
theorem LeanerVM.Semantics.compress_eq_reference (h : Vector UInt32 8) (m : Vector UInt32 16)
    (t : UInt64) (f : Bool) :
    (compress h m t (if f then 0xFFFFFFFF else 0) 0).toList.map UInt32.toBitVec =
      Hash.BLAKE2.Reference.F Hash.BLAKE2.blake2sParams 10
        (h.toList.map UInt32.toBitVec) (m.toList.map UInt32.toBitVec) t.toNat f
```

- **Difficulty: structural, medium.** About 200 to 300 lines: `mix_toBitVec`, `round_toBitVec`, then `Vector.foldl` over `sigma` against `(List.range 10).foldl`.
- Alternatively, unfold all 80 `G` calls on a 16-variable destructured vector, as machine-checked's `Blake2bSpec.lean` does for BLAKE2b.
- **Not** `decide`: it quantifies over all inputs.
- Checked numerically: 100 random `(h, m, t, f)` agree (scratch `Check2.lean`, below).

```lean
theorem LeanerVM.Protocol.Blake2sHash.digestBytes_blake2sBytes (data : List UInt8) :
    digestBytes (blake2sBytes data) = (Hash.blake2s ⟨data.toArray⟩).data.toList
-- corollaries, rfl/rw-level after the above:
theorem hashPair_bytes (l r : Digest) :
    digestBytes (hashPair l r) = (Hash.blake2s ⟨(digestBytes l ++ digestBytes r).toArray⟩).data.toList
theorem hashWords_bytes (ws : List K) :
    digestBytes (hashWords ws) = (Hash.blake2s ⟨(ws.flatMap kBytes).toArray⟩).data.toList
```

- **Difficulty: medium to hard.** About 300 lines.
  - Go through `Hash.BLAKE2.blake2s_eq` (`Equiv.lean:408`) to `Reference.hash blake2sParams [] [] [] 32`.
  - Prove that `wordsLE` of the zero-padded block is `blockWords`, and that the first word of `paramBlock` XORed into the IV gives `paramIv`.
  - The main work is an induction relating `absorb` (take/drop recursion with a running counter) to `Reference.hash` (`foldl` over `List.range (dd - 1)` with `chunks` and `getD`, counter `(i + 1) * 64`).
  - The final `take 32` is the whole 32-byte state.
- `digestBytes` is injective, so this pins `blake2sBytes` completely.
- Checked numerically for every length from 0 to 300 (scratch `Check.lean`).

Once §6 gap 1 is closed:

```lean
theorem LeanerVM.Semantics.compress_eq_compressWith (h m t) (f0 f1 : UInt32) :
    (compress h m t f0 f1).toList.map UInt32.toBitVec =
      Hash.BLAKE2.Reference.compressWith Hash.BLAKE2.blake2sParams 10   -- proposed name
        (h.toList.map UInt32.toBitVec) (m.toList.map UInt32.toBitVec) t.toNat f0.toBitVec f1.toBitVec
```

That makes `CompressCells`, and hence `Step`, `FlockSpec` and the table, statable against hash-specs. The circuit proof should keep `compress` as its target: `compress_getElem` unfolds it by `rfl` (`Blake2sCircuit.lean:292-299`), and `sound_rounds` walks `sigma.toList` (`:245`). Add the bridge as a corollary next to it.

## 6. Gaps in hash-specs

1. **The last-node flag and arbitrary flag words.**
   - `Reference.F` (`Reference.lean:108`) and `Fast.F` take one `f : Bool` and complement `v[14]` only. The leanVM opcode XORs two arbitrary 32-bit words into `v[14]` and `v[15]`, and leanerVM documents this as intended (`Semantics/Blake2s.lean:44-51`). leanerVM vendors hashlib `last_node` vectors (`tests/LeanerVMTests/Semantics/Blake2s.lean:70-98`).
   - Proposal: `Reference.compressWith P rounds h m t (f0 f1 : BitVec P.w)`, its `Fast` twin and `Equiv`, with `F P r h m t f = compressWith P r h m t (if f then allOnes else 0) 0`. Also add the `last_node` KATs to `HashTests/BLAKE2.lean`.
   - machine-checked needs the same for BLAKE2b (see `machine-checked.md`).
2. **A BLAKE2s `F` entry point.** `Hash.blake2bF` exists (`API.lean:47`) but there is no `Hash.blake2sF`. `Fast.F blake2sParams` works but is not public API.
3. **Length and size lemmas** for `Reference.F`, `Fast.F` and `Reference.hash`, needed to rebuild a `Vector`.
4. **Releases per downstream toolchain:** `v4.34.1` (§1).
5. Not needed: field hashes (leanerVM has none), Merkle trees and transcripts (they stay generic in leanerVM).

## 7. Discrepancies

No behavioural difference was found in the overlap. The concrete checks ran in hash-specs with `lake env lean`; the scratch files transcribe leanerVM verbatim and live in `evidence/leanervm-machine-checked/Check.lean` and `Check2.lean`.

| Check | Result |
|---|---|
| `digestBytes (blake2sBytes m) = (Hash.blake2s m).data.toList`, PRNG messages of every length 0..300 | all equal |
| `compress h m t (flag f) 0` vs `Hash.BLAKE2.Fast.F blake2sParams 10 … t.toNat f`, 200 random inputs, full 64-bit `t` | all equal |
| `compress` vs `Reference.F blake2sParams 10` over `BitVec 32`, 100 random inputs | all equal |
| leanerVM's vendored vectors (`"abc"` RFC 7693 App. B; `ramp 128` from hashlib) through `Hash.blake2s` | equal |
| hashlib `last_node` vector through leanerVM `compress` | reproduces; not expressible in hash-specs (gap 1) |

Parameter by parameter:

| Parameter | leanerVM | hash-specs | Verdict |
|---|---|---|---|
| Parameter block | `0x01010020` in word 0 (`Blake2sHash.lean:58`): nn = 32, kk = 0, fanout = depth = 1 | `Reference.paramBlock` with empty salt and personalisation | same |
| Rounds | `sigma.foldl` over all 10 rows (`Semantics/Blake2s.lean:107`) | `blake2sParams.rounds := 10` | same |
| Truncation | none: the digest is the 8 words | `.take 32` of 32 bytes | same |
| Counter | `UInt64`, wraps at 2^64 (`(t + data.length).toUInt64`) | `Nat`, split by `ofNat t` and `ofNat (t / 2^32)`, each reduced mod 2^32 | same for t < 2^64 |
| Flags | arbitrary `UInt32` words, plus last node | `Bool`, no last node | leanerVM is a strict superset (gap 1) |
| Empty message | one zero block at counter 0 (`(0 - 1) / 64 = 0`) | one zero block | same |
| Endianness | little-endian words and bytes | little-endian | same |

## 8. PR plan

**Conventions** (from `CONTRIBUTING.md`):

- Titles are `type(scope): subject`, lower-case and imperative, in ASCII only (no em or en dashes). Recent commits use scopes such as `protocol`, `semantics` and `arithmetization`.
- A large contribution needs a design issue first.
- A dependency PR must update `lakefile.toml`, `upstreams.json`, `lake-manifest.json` and `docs/dependencies.md` together, build the whole import cone, audit kernel axioms, and have "a named first-party consumer and a narrow import" (`docs/dependencies.md`).
- `./scripts/validate.sh` must pass. CI runs `policy.yml` (`scripts/audit-lean.sh`), `ci.yml`, `imports.yml` and the others.
- Reviews are triggered by a member commenting `/review` (`review.yml`).
- **No AI-attribution lines** in files (CONTRIBUTING "Licensing"). There is no CODEOWNERS file.
- New modules must be added to `LeanerVM.lean` or `tests/LeanerVMTests.lean`.

**Open PRs touching these files:**

- PR #119 (`Blake2sHash.lean`, the new `Blake2sFast`/`Blake2sHashFast`)
- PR #124 (`Blake2sHash.lean`, `Merkle.lean`, their tests)
- PRs #127 and #128 (`Blake2sHash.lean`)
- PR #142 (`Blake2sCircuit.lean`)
- PR #147 (`Merkle.lean`)
- PRs #82 and #83 (new `Semantics/Blake2sOutput.lean`)

This is a 43+ PR stack on issue #12. To avoid conflicts, every PR below adds **new files only** until the stack lands. No issue mentions hash-specs or blake.

### Prerequisites in hash-specs

| # | Title | Content | Size | Risk |
|---|---|---|---|---|
| H1 | `chore: release v4.34.1` (branch `release/v4.34.1` from tag `v4.34.0`) | `lean-toolchain` and Mathlib `rev` to `v4.34.1` in both packages; optionally cherry-pick `98c225d` for prebuilt oleans; tag `v4.34.1` | XS | the zk package's CompPoly must resolve under 4.34.1, built from source (ROADMAP §2.1 says this works) |
| H2 | `feat(blake2): compression with both flag words` | `Reference.compressWith`, `Fast.compressWith`, `Equiv`, `F = compressWith … 0`, `Hash.blake2sF`, `F_length`/`F_size`, hashlib `last_node` KATs; backport to the v4.34.1 line as `v4.34.1-patch1` | M | API naming; keep `F` unchanged |

### leanerVM

| # | Title | Files | Lakefile | Deleted / kept | Proof rework | Size | Risks |
|---|---|---|---|---|---|---|---|
| L1 | `feat(semantics): prove the BLAKE2s compression equal to hash-specs' reference` | new `LeanerVM/Semantics/Blake2sReference.lean`; new `tests/LeanerVMTests/Semantics/Blake2sReference.lean`; aggregates; `upstreams.json`; `docs/dependencies.md` (new table row); `lake-manifest.json` | add `[[require]] name = "hash-specs"`, `git = "https://github.com/Verified-zkEVM/hash-specs"`, `rev = "v4.34.1"` | everything kept | none (new theorems `iv_toNat`, `sigma_val`, `mix_toBitVec`, `round_toBitVec`, `compress_eq_reference`) | M (about 300 lines) | the dependency policy wants a named consumer: this PR is that consumer, so the require and the bridge go together. The kernel axiom audit now covers `Hash.*`; hash-specs' `HashTests/Axioms.lean` audits the same theorems. |
| L2 | `feat(protocol): prove blake2sBytes equal to hash-specs' BLAKE2s-256` | new `LeanerVM/Protocol/Blake2sHashReference.lean` and test | none | kept | none (new `digestBytes_blake2sBytes`, `hashPair_bytes`, `hashWords_bytes`) | M to L (about 300 lines) | conflicts with #127's `wordsOfBytes`/`digestOfBytes`; rebase after the stack |
| L3 | `feat(semantics): state the BLAKE2S opcode relation through hash-specs` (after H2) | `Semantics/Blake2sReference.lean`; bump the hash-specs `rev` | `rev = "v4.34.1-patch1"` | `compress` and `CompressCells` kept as definitions | none; `compress_eq_compressWith` is new, and `CompressCells` gets an equivalent `iff` form | S | none |
| L4 (optional, with the #119 author) | `perf(protocol): compute blake2sBytes through Hash.blake2s` | `Protocol/Blake2sHashFast.lean` (from #119) | none | could replace #119's `absorbFast`/`blockWordsFast` with `Hash.blake2s` plus L2 | `absorbFast_eq` becomes a corollary of L2 | S | **unverified**: speed of `Hash.blake2s` against #119's struct-of-words `compressFast`; run `bench/` first |

After that, re-pin hash-specs on each leanerVM toolchain bump, using our per-toolchain tags.

## 9. Open questions for the maintainers

1. Is a hash-specs dependency acceptable when its first consumer is a set of bridge theorems, with no executable use? (`docs/dependencies.md`: "named first-party use and a narrow import".)
2. Should we cut and maintain a `v4.34.1` line for you, or would you rather wait and adopt at your next bump (4.35)? Is a Clean 4.35 compatibility branch planned?
3. Does deployed leanVM ever set the last-node word or non-Boolean flag words? `Semantics/Blake2s.lean:44-51` says the constraints allow them. If yes, H2's `compressWith` is the right shared shape; is that name acceptable?
4. Would you take `Hash.BLAKE2.Fast` (with `Equiv`) in place of #119's own fast layer, subject to benchmarks?
5. Should the `CompressCells` bridge (L3) be the canonical statement in `Step.lean`, or stay a side theorem?
6. Should `Digest` stay `Vector UInt32 8`, or move to bytes to match `Hash.blake2s`? This affects `digestScalars` and the stack's `digestOfBytes`.
