# Upstreaming record: `machine-checked`

Prepared 2026-10-27 against hash-specs `98c225d`. Every claim about machine-checked cites a file and line at the commit below. Paths without a repository prefix are in machine-checked. Anything not checked is marked **unverified**.

## 1. Snapshot

| | |
|---|---|
| Repo | `Verified-zkEVM/machine-checked` |
| Commit | `5b1f8a5` (`5b1f8a543c4820945837ff19cae44c0c3401cd0f`), 2026-10-22 |
| Date examined | 2026-10-27 |
| Toolchain | `leanprover/lean4:v4.33.0` |
| Mathlib | `v4.33.0` = `db584cd6`, a direct require (`lakefile.toml`). It is used only by `Cases/Zip2005/Spec` and its closure. |
| Other pins | `riscv-zkvm@4634e41`, the `sp1-backend` branch (`lakefile.toml`); `Sail@8d57a8b`, transitive. **Unverified:** riscv-zkvm's toolchain at that pin. Its HEAD (`6810fc1`) is on v4.33.1. |
| Lakefile | `lakefile.toml`, with `moreLeanArgs = ["--tstack=400000"]` for the deep generated literals |
| Module system | **No.** No file in `MachineChecked/` or `Cases/` starts with `module`. hash-specs is in the module system; a classic file can import module files. leanerVM's classic tests do this, but **I have not checked it in this repo**. |

**Toolchain gap.** machine-checked is on v4.33.0; hash-specs is on v4.35.0, with releases only for v4.34.0, v4.35.0 and v4.35.0-patch1.

- **Require route.** This needs a hash-specs `v4.33.0` release.
  - **Verified 2026-10-27:** the hash-specs core builds unchanged on Lean 4.33.0 with Mathlib v4.33.0 (`db584cd`), with 0 warnings.
  - Moving machine-checked to v4.35.0 instead is blocked by riscv-zkvm, which is on 4.33.x. CONTRIBUTING says "The Lean toolchain is kept at the newest version the dependencies allow" (`CONTRIBUTING.md:77`).
- **Policy blocker.** `CONTRIBUTING.md:74-76`: "Code taken from another project is *ported*, not added as a dependency. It is copied, owned, and adapted … Record its origin in the module header and in the directory's `PROVENANCE.md`."
  - The project's own BLAKE2b spec was ported this way, from evm-asm (`Cases/Zip2005/Spec/Zip2005/Blake2b.lean:15-23`).
  - The leanVM case README already anticipates porting from us: "either this repository moves to the same toolchain and requires hash-specs, or the Mathlib-free reference module is what the guest's `compress` is proved against" (`Cases/LeanVM/README.md:26-33`).
- **Recommended route: port `Hash.BLAKE2.Reference`.**
  - The files are `Hash/BLAKE2/Reference.lean` (182 lines) and its only import, `Hash/Prelude/Bits.lean`, which has no imports. Both are Mathlib-free.
  - Copy them, pinned to a hash-specs tag, into machine-checked with a `PROVENANCE.md` entry.
  - `Fast`, `API`, `Equiv` and the KATs stay upstream. `Equiv` needs Mathlib (via `Hash.Init`), and machine-checked's proofs would target `Reference` anyway.
  - Effort: small. `Reference.lean` compiles on 4.33.0 (verified as part of the core build).

## 2. Overlap inventory

### 2a. Zip2005, BLAKE2b (the hash spec, as distinct from the machine-side model)

The **spec** is `Cases/Zip2005/Spec/Zip2005/Blake2b.lean`, namespace `Zip2005.Blake2b`, over `ℕ` lanes. Its compression function is ported from `evm-asm/EvmAsm/Stateless/SpecRef/PrecompilesHash.lean` (`:15-23`).

| Definition (file:line) | Signature / representation | hash-specs replacement |
|---|---|---|
| `M64` `:53` | `ℕ := 2^64` | none (BitVec 64) |
| `IV` `:57` | `List ℕ` | `Hash.BLAKE2.blake2bParams.IV` (`Reference.lean:160`), `blake2b_IV` |
| `sigma` `:64`, `mixTable` `:78` | `List (List ℕ)`, `List (ℕ×ℕ×ℕ×ℕ)` | `Hash.BLAKE2.SIGMA` (`Reference.lean:53`); the mix table is inlined in `Reference.round` |
| `rounds` `:83`, `blockBytes` `:86` | `12`, `128` | `blake2bParams.rounds`, `.blockBytes` |
| `rotr` `:91` | `ℕ → ℕ → ℕ`, `((x >>> n) \|\|\| (x <<< (64-n))) % M64` | `BitVec.rotateRight` in `Reference.G` |
| `G` `:95` | `List ℕ → (a b c d x y : ℕ) → List ℕ` | `Reference.G blake2bParams` over `List (BitVec 64)` (`Reference.lean:78`) |
| `mixRounds` `:113` | `(h m : List ℕ) (t0 t1 : ℕ) (f : Bool) → List ℕ` | the body of `Reference.F` |
| `compress` `:134` | `(h m : List ℕ) (t0 t1 : ℕ) (f : Bool) → List ℕ` | `Reference.F blake2bParams 12 h m (t0 + 2^64·t1) f` (`Reference.lean:108`); `Hash.blake2bF` (`API.lean:47`) |
| `leWords` `:143` | `List UInt8 → start → count → List ℕ` | `Reference.wordsLE` (on `chunks`) |
| `wordBytes` `:147`, `stateBytes` `:151` | `ℕ → List UInt8`, `List ℕ → List UInt8` | `Reference.bytesLE`, and `flatMap` |
| `paramWord0` `:158`, `initialState` `:168` | `(digestLen keyLen) (salt personal : List UInt8) → List ℕ` | `Reference.paramBlock` (`:120`), then XOR with the IV inside `Reference.hash` (`:140-146`) |
| `blockCount` `:182`, `absorbAux` `:187` | block count, and the fold over non-final blocks | `Reference.blocks` (`:127`) and the fold in `Reference.hash` |
| `blake2b` `:200` | `(personal : List UInt8) (nn : ℕ) (msg : List UInt8) → List UInt8`; unkeyed, no salt | **`Reference.hash blake2bParams [] [] personal nn msg`**; **`Hash.blake2bWith .empty .empty personal nn msg`** (`API.lean:24`) |
| `blake2b512` `:209` | `nn = 64` | same, with `nn = 64` |
| `blake2b_length` `:231`, `blake2b512_length` `:236` | output length | **no counterpart** (gap) |
| `Zip2005.prfExpand` `Spec/Zip2005/Prf.lean:30` | `blake2b512 prfExpandPersonalisation (seed ++ t)` | keep (Zcash-specific); restate over `Hash.blake2bWith … "Zcash_ExpandSeed" 64` |
| `prfExpandPersonalisation` `Spec/Zip2005/Constants.lean:124` | `"Zcash_ExpandSeed"` as bytes | keep |

The **machine-side model** is `Cases/Zip2005/Blake2b/Blake2bModel.lean`, namespace `Cases.Zip2005.B2b`. It works on `Word = BitVec 64`, from `notation "Word" => BitVec 64` in `riscv-zkvm/RiscvZkvm/Rv64/Word.lean:22`, read at riscv-zkvm HEAD.

| Definition (file:line) | Representation | hash-specs replacement |
|---|---|---|
| `rotr` `:16` | `x >>> n \|\|\| x <<< (64 - n)`, the compiled form | `BitVec.rotateRight` (lemma needed) |
| `Gw` `:21` | 4-tuple, second add associated as `a + y + b` (the compiled order) | `Reference.G` (reassociated) |
| `G_step`, `G_step_xb`, `G_step_by`, `G_step_xb_by` `:35-86` | match one machine step at a time | none (machine glue, keep) |
| `G` `:89`, `IV` `:93`, `sigma` `:97`, `mixTable` `:109`, `roundWith` `:114`, `round` `:126` | `List Word` | `Reference.G`/`round` over `List (BitVec 64)`: **the same carrier** |
| `initV` `:130` | `h t0 t1 (fb fn : Word)`; **has the last-node word `fn`** | inline in `Reference.F`; no `fn` |
| `roundsTo` `:138`, `compress` `:142` | `(h m : List Word) (t0 t1 fb fn : Word) → List Word` | `Reference.F blake2bParams 12 h m (t0.toNat + 2^64·t1.toNat) f` when `fb = if f then ones else 0` and `fn = 0` |
| `G_pos_*`, `round_eq_0..11`, `initV_eq`, `roundsTo_*`, `compress_eq`, `compress_length` `:148-275` | unfolding lemmas for the machine side | keep |

The **model-to-spec bridge** is `Cases/Zip2005/Blake2b/Blake2bSpec.lean`:

- `Gn` (`:44`) and `Gw_toNat` (`:55`);
- `G_toNat_*` (`:83-157`);
- `roundsTo_toNat` (`:168`);
- `compress_toNat` (`:190`):

```lean
(compress [h0..h7] [m0..m15] t0 t1 (if f then 0xFFFFFFFFFFFFFFFF#64 else 0#64) 0#64).map BitVec.toNat =
  Zip2005.Blake2b.compress [h0.toNat, …] [m0.toNat, …] t0.toNat t1.toNat f
```

**Spec-level glue** in `Blake2b/PrfExpandSpec.lean`:

- `blake2b_one_block` (`:28`);
- `prfH` (`:42`) and `prfH_toNat` (`:47`, by `decide`);
- `leos2ip_wordBytes` (`:52`);
- `leWords33/65/97` (`:75`, `:197`, `:231`);
- `prfExpand33_eq` (`:87`), `prfExpand65_eq` (`:211`), `prfExpand97_eq` (`:245`).

`Blake2b/PrfExpand169.lean` adds `blake2b_two_blocks` (`:26`) and `prfExpand169_eq` (`:65`).

**Generated or trace-derived files** (not spec): `Cases/Zip2005/Image/F_*.lean` (`DO NOT EDIT -- generated by lake exe gen-image`) and the trace segments `Blake2b/Seg1*.lean`, `Seg2.lean`, `Seg3.lean`, which the `Blake2bCompress*.lean` docstrings describe as "generated from the executor trace".

### 2b. How the Zip2005 correctness theorems are stated

All function specifications are `SafeN` in continuation form (`CONTRIBUTING.md` "One judgement"). There are three levels:

1. **Compression loop**: `compress1_128_spec` (`Blake2b/Blake2bCompress.lean:27-45`), with `_33/_41/_65/_97` variants. From the machine state at `pc = 0x78033260` with the state words at `wp` and the block at `blk`, every continuation that finds `Region wp (B2b.compress [h…] [m…] (c0+128) (c1+carry) (fz + 0xFFFF…FF) ((ln ||| fz) + 0xFFFF…FF))` is safe. Both flag words are computed from Rust enums; the last-node word is all ones only when both `ln` and `fz` are `0` ("yes").
2. **Spec serialisation**: for example, `prfExpand33_eq`:

   ```lean
   stateBytes ((compress prfH M 33#64 0#64 ones 0#64).map toNat) =
     prfExpand (stateBytes sk) [d]
   ```

   It is proved by `compress_toNat` and `blake2b_one_block`.
3. **Function correctness**: for example, `prf_expand_with_correct` (`Blake2b/PrfExpandWith.lean:93-117`). Every continuation whose 64 output bytes satisfy `stateBytes O' = Zip2005.prfExpand (stateBytes sk) [d]` is safe.

   The same shape appears in `prf_expand_apply2_correct` (`PrfExpandApply.lean:95`), and is consumed in `Bridge/SpecHashes.lean` (`psiX_correct` `:19`, `rivkIntX_correct` `:43`, `rcmRel_correct` `:75`), `Bridge/SpecKeys.lean`, and `Orchard/{Psi,Rcm,Rivk}.lean`.

### 2c. Zip2005, other hashes (no hash-specs counterpart)

- **Poseidon P128Pow5T3 over Pallas.**
  - Spec: `Cases/Zip2005/Spec/Zcash/Circuits/Poseidon/{Constants,Rounds,Pow5,Hash,…}.lean`. This is vendored halo2 `ConstantLength<2>`, `Hash.lean:1-25`.
  - Machine side: `Cases/Zip2005/Poseidon/*`.
  - Bridge: `Bridge/PoseidonBridge.lean`, which states the guest's Montgomery permutation is `Permute.value`, "4 full rounds, 28 paired partial rounds, 4 full rounds".
  - Field: `CompElliptic.Fields.Pasta.PallasBaseField`.
  - hash-specs has circomlib BN254 Poseidon and Poseidon2 (BN254/BabyBear/KoalaBear), but **not this instance**.
- **Sinsemilla**: `Spec/Zcash/Circuits/Specs/Sinsemilla.lean:55` (`hash`). Not in hash-specs' scope.

### 2d. The LeanVM BLAKE2s case

`Cases/LeanVM/Blake2s/` holds **no specification**:

- `Image/*.lean` and `Image/INDEX.tsv` are generated by `gen-image`. They list `compress` (644 words), `main`, `finish`, `memset`, and panic stubs.
- `Loaded.lean` holds the image facts: `codeWF`, `dataWF`, `entry`, and `*_decode`, all by `decide +kernel` (`:29-45`).

It **does not reuse leanerVM**: nothing imports `LeanerVM`, and the lakefile requires only riscv-zkvm and Mathlib. It also verifies a *different* leanVM:

| | machine-checked's LeanVM case | leanerVM |
|---|---|---|
| leanVM version | a RISC-V guest ELF from `leanEthereum/leanVM`, branch `riscv-exploration`, commit `9255db3e` (`Cases/LeanVM/README.md:9`) | pins leanVM `main@a386121f` (binary-field VM, with the BLAKE2S opcode) |
| BLAKE2s used | the guest is plain Rust and does **not** use leanVM's custom BLAKE2s instruction (`README.md:46-48`) | the opcode's compression |

The intended target is hash-specs: "a run of the guest with advice word `n` commits `n` and `BLAKE2s-256` of the `n` bytes `i mod 251`" (`README.md:32-33`). Nothing toward it is started (`README.md:63`).

## 3. How it is used

| Spec | Role | Consumers |
|---|---|---|
| `Zip2005.Blake2b.compress` | **proof target** of `B2b.compress_toNat` | `Blake2bSpec.lean` (3 mentions); `PrfExpandSpec.lean` (`compress_toNat` 3 times); `PrfExpand169.lean` (2) |
| `Zip2005.Blake2b.blake2b`, `blake2b512` | **proof target** via `blake2b_one_block`, `blake2b_two_blocks` | `PrfExpandSpec.lean` (4), `PrfExpand169.lean` (2); `assert_axioms Zip2005.Blake2b.blake2b` (`Spec/Zip2005.lean:95`); `#guard` KATs (`Spec/Zip2005/Blake2b.lean:264-280`) |
| `Zip2005.prfExpand` | **top-level proof target** | `prfExpand{33,65,97,169}_eq`, used in `PrfExpandWith.lean`, `PrfExpandApply.lean`, `Bridge/SpecHashes.lean` (3), `Bridge/SpecKeys.lean` (2), `Orchard/Psi.lean`, `Orchard/Rcm.lean`, `Orchard/Rivk.lean`. The statement layer uses it in `Spec/Zip2005/KeyComponents.lean` (6) and `Sending.lean` (6). Orchard-vector `#guard`s are in `Prf.lean:80-95`. |
| `B2b.compress` | machine-side model, the target of the RISC-V proofs | `Blake2bCompress{,_33,_41,_65,_97}.lean`, `Seg*`, `PrfExpand*`, `Main/MainAccept.lean`, `Main/MainWrapC.lean`, `Orchard/*` (16 files) |

There are **no executable uses**: the `#guard` conformance vectors are the only evaluation.

## 4. Representation gaps and adapter lemmas

| machine-checked | hash-specs | Adapter |
|---|---|---|
| `B2b`: `List Word` = `List (BitVec 64)` | `Reference`: `List (BitVec 64)` | none for the carrier. `rotr n x = x.rotateRight n` for `0 < n < 64`; reassociate `a + y + b`. |
| spec: `List ℕ` lanes `< 2^64` | `List (BitVec 64)` | `l.map BitVec.toNat`; `compress_toNat` already exists |
| `t0 t1 : Word` | `t : ℕ` | `t = t0.toNat + 2^64 * t1.toNat`, so `BitVec.ofNat 64 t = t0` and `t / 2^64 = t1.toNat` |
| `fb : Word` (all ones or zero) | `f : Bool` | `x ^^^ ones = ~~~x` |
| `stateBytes (ws.map toNat)` | `ws.flatMap (Reference.bytesLE blake2bParams)` | a lemma, provable per word |
| `leWords msg 0 16` | `Reference.wordsLE blake2bParams (padded block)` | a lemma: `leos2ip` of 8 bytes equals `bitsToNatLE ∘ bytesToBitsLSB`, with zero-extension of short reads |

These lemmas belong in machine-checked, or in the ported copy. hash-specs should provide the generic statements about `Reference.hash`: `hash_length`, and one-block and two-block unfoldings (§6).

## 5. Proposed bridge theorems

These go in machine-checked. Our names are checked in `Hash/BLAKE2/{Reference,API,Equiv}.lean` at `98c225d`.

**B1. The machine model is the reference compression.** Both sides are over `BitVec 64`, so this is the cheapest bridge, and it can replace the ℕ detour.

```lean
theorem Cases.Zip2005.B2b.compress_eq_reference (h m : List Word) (hh : h.length = 8)
    (hm : m.length = 16) (t0 t1 : Word) (f : Bool) :
    compress h m t0 t1 (if f then 0xFFFFFFFFFFFFFFFF#64 else 0#64) 0#64 =
      Hash.BLAKE2.Reference.F Hash.BLAKE2.blake2bParams 12 h m (t0.toNat + 2 ^ 64 * t1.toNat) f
```

- **Difficulty: structural, medium.** About 150 to 250 lines.
- Reuse `length16`, the `G_pos_*` lemmas and `round_eq_*`, as `Blake2bSpec.lean` does. Add a per-position `Reference.G` lemma (it writes in sequence with `getD`, with distinct indices), `rotr_eq_rotateRight`, and add reassociation by `ac_rfl`.
- Checked numerically: 100 random inputs (scratch `Check2.lean`).

**B2. The Zip2005 BLAKE2b spec is the reference hash.**

```lean
theorem Zip2005.Blake2b.blake2b_eq_reference (personal msg : List UInt8) (nn : ℕ)
    (hnn : nn ≤ 64) (hp : personal.length ≤ 16) :
    Zip2005.Blake2b.blake2b personal nn msg =
      Hash.BLAKE2.Reference.hash Hash.BLAKE2.blake2bParams [] [] personal nn msg
```

- **Difficulty: medium to hard.** About 300 lines.
- Compose `compress_toNat` (ℕ ↔ `B2b`) with B1 (`B2b` ↔ `Reference.F`).
- Relate `absorbAux`/`blockCount`/`leWords` to `Reference.blocks`/`chunks`/`wordsLE`.
- Show `initialState nn 0 [] personal = (zipWith xor IV (wordsLE paramBlock)).map toNat`, for which the bytes 48..63 carry the personalisation.
- `hp` is probably droppable: both sides truncate to 16 bytes (**unverified**).
- Checked numerically: lengths 0..299 with the personalisations `"Zcash_ExpandSeed"` and `[]`, and `nn ∈ {1, 32, 64}`, all equal to `Hash.blake2bWith` (scratch `Check.lean`).

**B3. PRF^expand through the byte API.** This needs the require route, because `blake2bWith_eq` lives in Mathlib-dependent `Equiv`.

```lean
theorem Zip2005.prfExpand_eq_blake2bWith (seed t : List UInt8) :
    Zip2005.prfExpand seed t =
      (Hash.blake2bWith .empty .empty ⟨prfExpandPersonalisation.toArray⟩ 64
        ⟨(seed ++ t).toArray⟩).data.toList
```

- Difficulty: **easy given B2**, via `Hash.BLAKE2.blake2bWith_eq` (`Equiv.lean:387`) with `key.size = 0 ≤ 128`.
- On the port route, state it against `Reference.hash` instead; it is then B2 with `nn = 64`.

**B4. The LeanVM guest target** (future, `Cases/LeanVM`):

```lean
-- the committed digest of a run with advice word n
digest = Hash.BLAKE2.Reference.hash Hash.BLAKE2.blake2sParams [] [] [] 32
           ((List.range n).map fun i => (i % 251).toUInt8)
-- or, with the require route, (Hash.blake2s ⟨…toArray⟩).data.toList via Hash.BLAKE2.blake2s_eq
```

The guest's `compress` (`F_10000038`, 644 words) would be proved against `Reference.F blake2sParams 10` the same way `B2b.compress` is for BLAKE2b. That needs a 32-bit model analogous to `Blake2bModel.lean`.

## 6. Gaps in hash-specs

1. **The last-node flag.** `compress1_128_spec` carries the last-node word `(ln ||| fz) - 1`, and `B2b.initV` has `fn`. Today the spec instantiates `fn = 0` only (`Blake2bSpec.lean:13-14`). It is the same gap as for leanerVM: `Reference.compressWith P r h m t f0 f1` with `F` as its special case.
2. **Lemmas about `Reference.hash`**:
   - `hash_length : nn ≤ 8 * (P.w / 8) → (Reference.hash P key salt personal nn msg).length = nn`;
   - a one-block unfolding for `1 ≤ msg.length ≤ bb`;
   - a two-block unfolding.

   machine-checked proves all three for its own spec (`blake2b_length` `:231`, `blake2b_one_block`, `blake2b_two_blocks`). Every machine-code proof of a short-message hash needs them.
3. **`Reference.F_length`.**
4. **Poseidon P128Pow5T3 over Pallas** (t = 3, α = 5, 8 full and 56 partial rounds, halo2 constants). Our `Hash/ZK/Poseidon` is generic over `[Field F]`, so this is a new parameter set, plus a CompElliptic/Mathlib Pallas field. CompPoly also has Pasta (ROADMAP §1).
5. **A release or porting story for v4.33.** Either a tested `v4.33.0` tag, or a documented "port `Reference.lean` + `Prelude/Bits.lean`" recipe that names their Mathlib-free status as an API promise. ROADMAP §2.1 keeps this split possible but does not promise it.

## 7. Discrepancies

No behavioural difference was found. The checks ran in hash-specs with `lake env lean`, on verbatim transcriptions in `evidence/leanervm-machine-checked/Check.lean` and `Check2.lean`:

| Check | Result |
|---|---|
| `Zip2005.Blake2b.blake2b pers nn m` vs `Hash.blake2bWith .empty .empty pers nn m`, `pers ∈ {"Zcash_ExpandSeed"}`, `nn ∈ {1, 32, 64}`, lengths 0..299; and `blake2b [] 64 m = Hash.blake2b m` | all equal |
| `Zip2005.Blake2b.compress` vs `Hash.blake2bF 12`, 200 random inputs, both `f` values | all equal |
| `B2b.compress … (flag f) 0#64` vs `Reference.F blake2bParams 12`, 100 random inputs | all equal |
| RFC 7693 App. A `"abc"` through the transcription and `Hash.blake2b` | equal |

Domain-edge differences. These are outside the inputs that are ever used, but a bridge needs a hypothesis for each:

- `paramWord0` ORs `digestLen` as a natural number (`Blake2b.lean:158-159`), while `Reference.paramBlock` uses `nn.toUInt8`. They differ for `nn ≥ 256`; the bridge needs `nn ≤ 64`.
- `Zip2005.Blake2b.compress` XORs the raw `t0`, `t1 : ℕ` (`:115-116`), with no reduction. It differs from `Reference.F` if `t0 ≥ 2^64`.

Stale text:

- `Cases/LeanVM/README.md:27` and `ROADMAP.md:111` link `https://github.com/dhsorens/hash-specs`. The repo is now `Verified-zkEVM/hash-specs`.
- `Spec/Zip2005/Blake2b.lean:9-13` says "Nothing in the Lean ecosystem has BLAKE2b as a *hash*". hash-specs now does.

## 8. PR plan

**Conventions** (from `CONTRIBUTING.md`):

- Titles are `<type>(<scope>): <subject>`. Types are `feat`, `fix`, `proof`, `doc`, `refactor`, `perf`, `test`, `chore` and `ci`; scopes are a directory or case (`zip2005`, `lprog`, …).
- One change per PR.
- No `sorry`, `axiom` or `native_decide`, and **zero new warnings**.
- Run `#print axioms` on new theorems.
- A changed statement keeps a `@[deprecated] alias`.
- Ported code goes in with provenance and its licence notice.
- CI builds only the quick cases, which include `Cases.LeanVM.Blake2s.Loaded` but **not** the Zip2005 BLAKE2b proofs. Those need `workflow_dispatch` with `full: true` or a local `lake build Cases.Zip2005.Blake2b.*`.
- I found no AI-disclosure rule. `AGENTS.md` is the agent entry point.
- There is no CODEOWNERS file.
- Open PRs: #16 ("docs: propose a library shared with catcrypt-compiler", which could become the home for ported specs) and #17 (Lprog milestone A). Neither touches the BLAKE2 or LeanVM files. No issues mention blake or hash-specs.

### Prerequisites in hash-specs

| # | Title | Content | Size |
|---|---|---|---|
| H1 | `feat(blake2): lemmas for short messages` | `Reference.F_length`, `Reference.hash_length`, `Reference.hash_one_block`, `Reference.hash_two_blocks` | S to M |
| H2 | `feat(blake2): compression with both flag words` | shared with leanerVM's H2 | M |
| H3 (only for the require route) | `chore: release v4.33.0` | backport branch at Lean and Mathlib v4.33.0; builds unchanged (verified) | S to M |
| H4 | `doc: document the Mathlib-free porting surface of Hash.BLAKE2.Reference` | README note that `Reference.lean` + `Prelude/Bits.lean` import only core | XS |

### machine-checked (port route, recommended)

| # | Title | Files | Lakefile | Deleted / kept | Proof rework | Size | Risks |
|---|---|---|---|---|---|---|---|
| M1 | `doc(leanvm): point the BLAKE2s specification at Verified-zkEVM/hash-specs` | `Cases/LeanVM/README.md`, `ROADMAP.md` | none | none | none | XS | none |
| M2 | `feat(spec): port hash-specs' BLAKE2 reference` | new `Cases/HashSpecs/BLAKE2/Reference.lean`, `Cases/HashSpecs/Prelude/Bits.lean` (location for the maintainers to decide; PR #16 may supply a shared home), `PROVENANCE.md` with the hash-specs tag and Apache-2.0 | none | none | none | S | compiles on 4.33.0 with 0 warnings (verified with the core build). |
| M3 | `proof(zip2005): the BLAKE2b model is the reference compression` | new `Cases/Zip2005/Blake2b/ReferenceBridge.lean` (B1) | none | kept | none | S to M | heartbeat budget; `Blake2bSpec.lean` already uses `maxHeartbeats 4000000` |
| M4 | `proof(zip2005): BLAKE2b and PRF^expand are the reference hash` | same file, or `ReferenceHash.lean` (B2, B3 on `Reference`) | none | kept | none | M to L | the `leWords`/`chunks` induction |
| M5 (optional) | `refactor(zip2005): define BLAKE2b by the hash-specs reference` | `Spec/Zip2005/Blake2b.lean` (`blake2b := Reference.hash blake2bParams [] [] personal nn`; delete `rotr/G/mixRounds/compress/absorbAux/…`), `Blake2bSpec.lean` (replace `compress_toNat` by B1), `PrfExpandSpec.lean` and `PrfExpand169.lean` (`blake2b_one_block`/`two_blocks` from H1; `prfExpand*_eq` re-proved through B1), `Spec/Zip2005.lean` (`assert_axioms`) | none | delete the ℕ compression; keep the `#guard` KATs, `prfExpand`, `prfH` | `prfExpand{33,65,97,169}_eq` (4 theorems) and `blake2b_one_block`/`two_blocks`; downstream `Bridge/*` and `Orchard/*` are unchanged if the theorem statements are kept | M | changes the trusted statement (`Spec/` is the statement layer); a maintainers' call |
| M6 (later) | `proof(leanvm): the blake2s guest commits BLAKE2s-256 of its input` | `Cases/LeanVM/Blake2s/*` (a 32-bit model as in `Blake2bModel.lean`, then the B4 statement) | none | none | new | L to XL | needs the leanVM step instance first (`Cases/LeanVM/README.md:42-61`) |

**Require-route variant.** After H3, M2 becomes `chore: require hash-specs v4.33.0`, with `[[require]] name = "hash-specs"`, `git = "https://github.com/Verified-zkEVM/hash-specs"`, `rev = "v4.33.0"`. B3 can then target `Hash.blake2bWith`. This conflicts with `CONTRIBUTING.md:74-76` unless the maintainers make an exception.

## 9. Open questions for the maintainers

1. Port or require? CONTRIBUTING mandates porting. Would you make an exception for a canonical org spec, given per-toolchain releases?
2. If porting, where should ported org specs live (`Cases/<x>/Spec`, or the shared library proposed in #16)? Should the ported `Reference` be kept byte-identical to a hash-specs tag, so that a later bridge to the upstream is `rfl`?
3. Should `Zip2005.Blake2b` (ported from evm-asm) be replaced by the hash-specs reference (M5), or should it stay the trusted statement with B2 as evidence?
4. Is a hash-specs `v4.33.0` worth producing? When do you expect riscv-zkvm to move past 4.33?
5. For the leanVM guest: is the target the RISC-V `riscv-exploration` line only, or will the case also cover the custom BLAKE2s instruction? If so, the instruction semantics should be bridged to leanerVM's `compress`/`CompressCells` and to hash-specs' two-flag compression (leanerVM H2).
6. Is Pallas Poseidon P128Pow5T3 wanted in hash-specs (§6 gap 4), to replace the vendored halo2 constants as the reference?
