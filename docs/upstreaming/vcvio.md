# Upstreaming record: VCVio

Scope: every hash definition in `Verified-zkEVM/VCVio` and everything that consumes one. The hash
code is in three places:

- `VCVio/Algorithms/{Keccak,KeccakPrefix,Sha2,Encoding}.lean`: pure-Lean SHA-2, SHA-3, SHAKE,
  Keccak-256, HMAC and MGF1. The hash-specs ROADMAP §1 table still cites the old paths
  `HashSig/SLHDSA/Concrete/{Keccak,Sha2}.lean`, which no longer exist.
- `Extern/Hashing.lean`: C SHA-3/SHAKE through FFI, used only by the native ML-KEM, ML-DSA and
  Falcon executables.
- The SLH-DSA instantiations in `HashSig/SLHDSA/{Concrete,C13,Security}`, which consume the pure
  defs.

`LatticeCrypto` (ML-KEM, ML-DSA, Falcon) has no concrete hash. It is parametric over a
`Primitives` structure (`LatticeCrypto/MLKEM/Primitives.lean:24`, `MLDSA/Primitives.lean:43`,
`Falcon/Primitives.lean:120`). `Examples/Pedersen.lean` is a discrete-log commitment over `ZMod 101`
and has no hash. There is no Poseidon, BLAKE or RIPEMD anywhere (`grep -ril` returns 0 hits).

**Bottom line.**

- **Easiest adoption in the org.** VCVio is already on Lean v4.35.0 with Mathlib `v4.35.0`, and
  every shared transitive pin is the same commit as ours, so no toolchain work is needed.
- **Same functions as ours.** Its pure-Lean hashes are byte-for-byte the functions hash-specs
  exports, on the same representation (`ByteArray → ByteArray`). I checked this directly: 5,878
  differential checks show 0 mismatches, and all of VCVio's own hash KATs pass when run on
  hash-specs (§7).
- **Small proof surface.** Only about 40 lines of proof unfold the concrete hash
  (`KeccakPrefix.lean` and `ByteConformance.lean:110–137`), plus size `simp` lemmas. Everything
  else uses the hash as an opaque function or as a random oracle.
- **Gaps in hash-specs.**
  1. **HMAC-SHA-256/512 and MGF1-SHA-256/512**, which FIPS 205 SLH-DSA-SHA2 needs.
  2. **Output-size lemmas** on the byte API.
  3. **A performance bug.** `Hash.Keccak.Fast.squeeze` runs one wasted Keccak-f per call, so
     every single-block SHA-3, SHAKE or Keccak-256 costs twice as much as it should. VCVio's
     per-PR CI runs SLH-DSA-SHAKE signing on pure-Lean SHAKE, so this would show up there.
- **VCVio policy forbids compatibility shims** (`docs/agents/gotchas.md:295–298`). The plan is
  therefore a full cutover, not deprecate-and-alias.
- **Main coordination risk.** Open draft PR #910 (Cryptol bridge) proves theorems about
  `VCVio.Algorithms.Sha2` internals (`bsig0`, `compress`, `RoundState`).

**Priority: high value, low cost.** It removes the org's fourth Keccak copy and second SHA-2 copy.

## 1. Snapshot

| Item | Value |
|---|---|
| Repo | `Verified-zkEVM/VCVio`, HEAD `575962c` (`575962c249de3df7542009b1a60d59950d44072e`, 2026-10-26, "Interpret quantum programs and query weights with PolyFun's indexed fold (#917)"), read 2026-10-27 |
| Toolchain | `leanprover/lean4:v4.35.0` (`lean-toolchain`) |
| Lakefile | `lakefile.lean` (DSL, not TOML) |
| Direct requires | `PolyFun` @ `4181c822…` (`lakefile.lean:73–75`); `mathlib` @ `v4.35.0` (`lakefile.lean:77`). Hax and Aeneas are commented out (`:53–65`). |
| Manifest | mathlib `56a005855e`, batteries `66e469188f`, aesop `4a174c490d`, Qq `dce0ad79c4`, plausible `dfa4f38190`, proofwidgets `df72b022e5`, importGraph `a41f0e9a4d`, LeanSearchClient `d6b4c7be5b`, Cli `c24fe6078c`, cslib `5b56df9936` (v4.35.0), PolyFun `4181c82238`. **Every package shared with hash-specs' manifest is pinned to the identical commit.** |
| Module system | Yes, throughout (`module`, `@[expose] public section`; `CONTRIBUTING.md` "Module Scopes") |
| Native code | `extern_lib leanhashing` compiles `csrc/hashing/lean_hashing_ffi.c` against the `third_party/mlkem-native` submodule (`lakefile.lean:168–185`). Without the submodule it builds an empty stub. |
| Toolchain gap | **None.** v4.35.0 = v4.35.0 |

**Does adoption force a toolchain bump? No.** Require `hash-specs` at `v4.35.0-patch1`. The
Mathlib cache and our prebuilt oleans (`preferReleaseBuild`) both apply. The only thing to watch
is future bumps. VCVio moves fast (three recent merged PRs, #909, #911 and #914, are PolyFun repins), so
each VCVio toolchain bump will need a matching hash-specs release tag. CompPoly already works this
way.

## 2. Overlap inventory

Representation everywhere: byte strings are `ByteArray`. Keccak state is `Array UInt64` (25
lanes, `x + 5y`). SHA-2 state is `Array UInt32` or `Array UInt64`, read with `!` indexing.

### 2.1 `VCVio/Algorithms/Keccak.lean` (namespace `VCVio.Algorithms.Keccak`)

| Line | VCVio name | Signature | hash-specs replacement |
|---|---|---|---|
| 30 | `rhoLUT` | `Array ℕ` | `Hash.Keccak.Fast.rhoRotations` (internal) |
| 35 | `piLUT` | `Array ℕ` | `Hash.Keccak.Fast.pi` (internal) |
| 40 | `roundConstants` | `Array UInt64` | `Hash.Keccak.Fast.roundConstantWords` |
| 49 | `rotl64` | `UInt64 → ℕ → UInt64` | no direct counterpart (internal) |
| 53 | `round` | `Array UInt64 → UInt64 → Array UInt64` | `Hash.Keccak.Fast.round : Array UInt64 → Nat → Array UInt64` (takes the round index, not the constant) |
| 67 | `f1600` | `Array UInt64 → Array UInt64` | `Hash.Keccak.Fast.keccakF` (agrees on 50 random states, §7) |
| 71 | `absorb` | `ByteArray → (rate) → (padByte : UInt8) → Array UInt64` | `Hash.Keccak.Fast.pad` + `absorbBlock` (internal to `sponge`) |
| 86 | `squeeze` | `Array UInt64 → ℕ → ByteArray` (one block) | `Hash.Keccak.Fast.rateBytes` / `squeeze` (different shape) |
| 97 | `squeezeFullBlocks` | `Array UInt64 → ℕ → ℕ → Array UInt64 × ByteArray` | `Hash.Keccak.Fast.squeeze` |
| 112 | `squeezeXof` | `Array UInt64 → ℕ → ℕ → ByteArray` | `Hash.Keccak.Fast.squeeze` + `extract` |
| 127 | `keccak256` | `ByteArray → ByteArray` | `Hash.keccak256` |
| 130/133/136/139 | `sha3Digest256/224/384/512` | `ByteArray → ByteArray` | `Hash.sha3x256/224/384/512` |
| 142 | `shake128` | `ByteArray → ℕ → ByteArray` | `Hash.shake128` |
| 147 | `shake256` | `ByteArray → ℕ → ByteArray` | `Hash.shake256` |
| 90, 104, 119, 150–168 | `squeeze_size`, `squeezeFullBlocks_size`, `squeezeXof_size`, `shake128_size`, `shake256_size`, `sha3Digest*_size` (all `@[simp]`) | `(f m …).size = …` | **no counterpart** (gap G2) |

### 2.2 `VCVio/Algorithms/KeccakPrefix.lean`

| Line | VCVio name | hash-specs replacement |
|---|---|---|
| 27, 36, 55 | `take_toList_squeeze`, `take_toList_squeezeFullBlocks`, `take_toList_squeezeXof` | internal; no counterpart needed |
| 99 | `take_toList_shake256 (x) (hnm : n ≤ m) : (shake256 x m).data.toList.take n = (shake256 x n).data.toList` | `(Hash.Keccak.shake256_prefix x hnm).symm` (`Hash/Keccak/Equiv.lean:473`). Checked in scratch: it typechecks as a one-liner. |
| 104 | `take_toList_shake128` | `(Hash.Keccak.shake128_prefix x hnm).symm` (`Equiv.lean:466`) |

### 2.3 `VCVio/Algorithms/Sha2.lean` (namespace `VCVio.Algorithms.Sha2`)

| Line | VCVio name | Signature | hash-specs replacement |
|---|---|---|---|
| 33, 38, 214–231 | `iv`, `iv224`, `iv512`, `iv384`, `iv512Trunc224/256` | `Array UInt32/UInt64` | `Hash.SHA2.initialHash*` (`List Nat`, `Hash/SHA2/Constants.lean:51–104`) |
| 43, 234 | `k`, `k512` | `Array UInt32/UInt64` | `Hash.SHA2.K256`, `K512` (`List Nat`). These are equal after `map ofNat` (checked, §7). |
| 54–69, 257–275 | `rotr`, `ch`, `maj`, `bsig0/1`, `ssig0/1`, `rotr64`, `ch64`, `maj64`, `bsig*Sha512`, `ssig*Sha512` | word ops | `Hash.SHA2.Fast.{Ch, Maj, bigSigma, smallSigma}` at `Hash.SHA2.sha256.bigSigma0` etc. (generic over `[Word α]`) |
| 72, 92 | `RoundState`, `round256` | 8-field struct | `Hash.SHA2.Reference.Vars`, `Hash.SHA2.Fast.round` |
| 98, 102 | `u32be`, `u64be` | `UInt32 → ByteArray` | `Hash.ByteArray.pushUInt32BE` / `pushUInt64BE` (different shape) |
| 108, 278 | `pad`, `pad512` | `ByteArray → ByteArray` | `Hash.SHA2.Fast.pad Hash.SHA2.sha256` |
| 118–147 | `readWord256`, `loadSchedule256`, `expandSchedule256`, `runRounds256`, `feedForward256` | internal | `Hash.SHA2.Fast.schedule` and the `compress` body |
| 150 | `compress` | `Array UInt32 → ByteArray → Nat → Array UInt32` | `Hash.SHA2.Fast.compress Hash.SHA2.sha256 K st m base`. Equal on 200 random states and offsets, including short states and reads past the end (§7). |
| 287 | `compress512` | `Array UInt64 → ByteArray → Nat → Array UInt64` | `Hash.SHA2.Fast.compress Hash.SHA2.sha512 K st m base` (equal, §7) |
| 154, 316 | `stateBytes32`, `stateBytes64` | serialisation | internal to `hashWith` |
| 163, 325 | `sha256Family`, `sha512Family` | `(initial) → (outLen) → ByteArray → ByteArray` | `Hash.SHA2.Fast.hashWith α P` |
| 172, 175 | `sha224`, `sha256` | `ByteArray → ByteArray` | `Hash.sha224`, `Hash.sha256` |
| 334–343 | `sha384`, `sha512`, `sha512Trunc224`, `sha512Trunc256` | `ByteArray → ByteArray` | `Hash.sha384`, `Hash.sha512`, `Hash.sha512t224`, `Hash.sha512t256` |
| 177–181, 345–355 | `sha*_size` (`@[simp]`) | size equations | **no counterpart** (G2) |
| 184, 366 | `mgf1`, `mgf1Sha256` | `ByteArray → Nat → ByteArray` | **no counterpart** (G1) |
| 358 | `mgf1Sha512` | same | **no counterpart** (G1) |
| 192, 200, 207 | `hmacKey0`, `xorConst`, `hmacSha256` | `(key msg : ByteArray) → ByteArray` | **no counterpart** (G1) |
| 369, 377 | `hmacKey0Sha512`, `hmacSha512` | same | **no counterpart** (G1) |
| 384–427 | `InputError`, `sha256InputLengthValid`, `sha512InputLengthValid`, `sha256Checked`, `sha512Checked`, `mgf1Sha256/512Maximum`, `mgf1Sha256/512Checked` | domain-checked wrappers | no counterpart. Only tests use them (`VCVioTest/Algorithms/Hash.lean:167–170, 192–199`), so keep them in VCVio. |

`VCVio/Algorithms/Encoding.lean:23` `natToBytesBE` is a generic big-endian integer encoder. It is
used by SLH-DSA addressing (`HashSig/SLHDSA/Encoding.lean`, `EncodingLemmas.lean`,
`Security/KeySeparation.lean`, `SHAKE128s/Bridge/Encodings.lean`). It is not a hash: **keep it.**

### 2.4 `Extern/Hashing.lean` (namespace `FFI.Hashing`) and `Extern/MLKEM/FFI.lean`

| Line | Name | Signature | Backed by | hash-specs replacement |
|---|---|---|---|---|
| `Hashing.lean:24` | `sha3_256` | `@& ByteArray → ByteArray`, `@[extern "lean_sha3_256"] opaque` | `mlk_sha3_256` (`csrc/hashing/lean_hashing_ffi.c:23–29`) | `Hash.sha3x256` |
| `:28` | `sha3_512` | same | `mlk_sha3_512` (`.c:31–37`) | `Hash.sha3x512` |
| `:32` | `shake256` | `@& ByteArray → USize → ByteArray` | `mlk_shake256` (`.c:39–45`) | `Hash.shake256 m n.toNat` |
| `:36` | `shake128` | same | incremental `mlk_shake128_*` (`.c:47–71`) | `Hash.shake128 m n.toNat` |
| `MLKEM/FFI.lean:37–43` | `FFI.sha3_256`, `sha3_512`, `shake256`, `shake128` | `abbrev` re-exports of the above | | follow the above |

## 3. How it is used

### 3.1 Proof targets (definitions that proofs unfold)

Only these unfold a VCVio hash body. All other SLH-DSA proofs treat the primitives either
abstractly (`Primitives` fields, ROM oracles), or through `shakeAnswer`/`shakeThash`/… without
unfolding `shake256`.

| Site | What it depends on | Rework |
|---|---|---|
| `VCVio/Algorithms/KeccakPrefix.lean:27–106` (whole file) | `squeeze`, `squeezeFullBlocks`, `squeezeXof` bodies | **Delete**, and replace with `Hash.Keccak.shake{128,256}_prefix` |
| `HashSig/SLHDSA/Security/ByteConformance.lean:115–118` `Keccak.toList_data_squeeze` | `simp [squeeze]` | delete (no external users; grep finds none) |
| `ByteConformance.lean:121–123` `Keccak.toList_data_squeezeXof_of_lt` | `simp [squeezeXof, …, squeezeFullBlocks]` | delete (no external users) |
| `ByteConformance.lean:127–135` `Keccak.take_toList_data_shake256` | `simp only [shake256]`, then the two above | re-prove as `(Hash.Keccak.shake256_prefix x hnm).symm`. The `hm : m < 136` hypothesis becomes unused, so either drop it or keep the statement shape. Public, but no external users. |
| `ByteConformance.lean:140–143` `toList_byteArrayPrefixOrZero_shake256` | `simp` with `shake256_size` | needs `Hash.shake256_size` (G2) |
| `ByteConformance.lean:205` (in `toList_prefixBytes_shakeAnswer_of_le`) | `VCVio.Algorithms.Keccak.take_toList_shake256` | `(Hash.Keccak.shake256_prefix _ hnm).symm` |
| `HashSig/SLHDSA/Concrete/Prehash.lean:143–145` `Algorithm.digestRaw_size` (`@[simp]`) | `simp [digestRaw, outputLength]` with all twelve `*_size` lemmas, including `squeeze_size` for the SHAKE prehash | needs size lemmas for `Hash.sha224…sha512t256`, `sha3x*`, `shake128`, `shake256` (G2). Used by `Prehash.lean:159–170`. |
| `VCVioTest/Algorithms/Hash.lean:33–43` | two `example`s: one-call `simp` on all size lemmas | same (G2); the file is a "one-call simp gate" per the PR template |

Downstream of these, `shakeRomScheme_map_shakeAnswer*` (`ByteConformance.lean:329–366`), and
through it `Wire.lean:85–95` and `HashSigTest/SLHDSA/ByteModel.lean:78–128`, need no change once
the lemmas above are re-proved with the same statements. `shakeAnswer` (`:188–189`) just names
`Keccak.shake256`. Under hash-specs it names `Hash.shake256`, and every theorem about it goes
through the prefix and size lemmas.

### 3.2 Executable uses (direct swap)

| File | Lines | Calls | Swap |
|---|---|---|---|
| `HashSig/SLHDSA/Concrete/FIPS.lean` | imports 9–10, opens 41–42; 135, 142, 150, 152, 159, 161, 177, 181, 271, 273, 275 | `sha256`, `sha512` | `Hash.sha256`, `Hash.sha512` |
| same | 167, 169 | `hmacSha256`, `hmacSha512` | stay in VCVio until G1 |
| same | 178, 182 | `mgf1Sha256`, `mgf1Sha512` | stay in VCVio until G1 |
| same | 303, 308, 313, 318, 323, 329, 335 | `shake256` | `Hash.shake256` |
| `HashSig/SLHDSA/Concrete/Instance.lean` (SHA2-128-24) | import 9, open 41; 85, 101, 111 | `sha256` | `Hash.sha256` |
| same | 105, 112 | `hmacSha256`, `mgf1` | G1 |
| `HashSig/SLHDSA/Concrete/Prehash.lean` | imports 9–10, open 29; 130–139 | `Sha2.sha224…sha512Trunc256`, `Keccak.sha3Digest*` | `Hash.sha224…sha512t256`, `Hash.sha3x*` |
| same | 140, 141 | `Keccak.squeeze (Keccak.absorb input 168 0x1f) 32`, `… 136 … 64` | `Hash.shake128 input 32`, `Hash.shake256 input 64` (equal on all 308 lengths tried, §7) |
| `HashSig/SLHDSA/C13/Concrete.lean` | import 9, open 36; 64, 67, 70, 73, 76, 81, 86 | `keccak256` | `Hash.keccak256` |
| `HashSig/SLHDSA/Security/ByteConformance.lean` | import 10; 141, 189, 195, 203, 211 | `Keccak.shake256` | `Hash.shake256` |
| `HashSigTest/SLHDSA/ByteModel.lean` | open 51; 178–179, 188–192 | `Keccak.shake256`, `Keccak.shake128` | `Hash.*` |
| `HashSigTest/SLHDSA/PrimitiveTests.lean` | opens 26–27; 159, 163 | `sha256` | `Hash.sha256` |
| `VCVioTest/Algorithms/Hash.lean` | imports 9–10, open 27; 87–259 | all of the above | `Hash.*`, plus the local HMAC/MGF1 |

**Count** (excluding imports and opens):

- 5 HashSig source files, with 51 call sites: FIPS 22, Instance 5, Prehash 12, C13 7,
  ByteConformance 5. Of these, 6 are HMAC/MGF1 calls that stay on VCVio's own definitions until
  G1.
- 3 test files: ByteModel 6, PrimitiveTests 2, and the whole of `VCVioTest/Algorithms/Hash.lean`.
- 3 proof blocks (§3.1).

Docs and scripts that name the modules and need text updates:

- `docs/design/repository-layout.md:76–82`
- `docs/design/slh-dsa-classical-rom-bound.md:99`
- `docs/design/slh-dsa-status-and-roadmap.md:31, 210`
- docstrings in `scripts/InitSweep.lean:186` and `scripts/VCVioInitSweepTestFixtures/Clean/Negatives.lean:44`. Both cite `VCVio.Algorithms.Keccak.piLUT` as the one `List.range` in the swept tree.

### 3.3 FFI uses (Extern only; opaque, no proofs)

| File:line | Call |
|---|---|
| `Extern/MLKEM/Instance.lean:73` | `FFI.shake128 input 840` (SampleNTT) |
| `:87` | `FFI.shake256 input (64·η)` (PRF) |
| `:94`, `:99` | `FFI.sha3_512` (G), `FFI.sha3_256` (H) |
| `:121` | `FFI.shake256 … 32` (J) |
| `Extern/MLDSA/Sampling.lean:41, 45, 56, 192` | `FFI.Hashing.shake256` |
| `:92` | `FFI.Hashing.shake128 input 4096` (RejNTTPoly) |
| `Extern/Falcon/Sampling.lean:43, 50, 57` | `FFI.Hashing.shake256` |
| `Extern/Falcon/SamplerZ.lean:66, 71` | `FFI.Hashing.shake256` (PRNG init and refill) |
| `Extern/Falcon/Sign.lean:91` | `FFI.Hashing.shake256 … 96` |
| `LatticeCryptoTest/MLKEM/Main.lean:40–62, 171` | the FFI hashes themselves, as smoke tests |

**Are KATs run through them?** Yes, but only on the nightly path. `mlkem_test`, `mldsa_test` and
`falcon_test` (`lakefile.lean:447–457`) run only under `lake test -- --ffi`
(`lakefile.lean:427–428`). That is the "FFI Nightly Check" workflow
(`.github/workflows/ffi-check.yml:1–13`: cron `0 7 * * *` plus manual dispatch), and the PR
template forbids "native FFI test executables on the PR path". The per-PR `lake test` runs the
SLH-DSA executables on the **pure-Lean** hashes instead:

- `slhdsa_kat`: SHA2-128-24 verify (`:459`)
- `slhdsa_c13_kat`: Keccak-256 verify (`:463`)
- `slhdsa_primitive_tests` (`:471`)
- `slhdsa_external_tests` (`:495`): pre-hash, all twelve digests
- `slhdsa_byte_model_tests` (`:502`): SLH-DSA-SHAKE-128f, 192f and 256f keyGen, sigGen
  (deterministic and hedged) and sigVer against NIST ACVP (`HashSigTest/SLHDSA/ByteModel.lean:31–39`)

The SHAKE signing vectors make tens to hundreds of thousands of `shake256` calls on short inputs.
**Pure-Lean Keccak throughput is therefore on VCVio's per-PR critical path. FFI hashing is not.**

## 4. Representation gaps and adapter lemmas

**There are none at the API level.** Both sides use `ByteArray → ByteArray` and
`ByteArray → Nat → ByteArray` with identical semantics. The SLH-DSA code already converts at its
own boundary (`bytesToByteArray`, `byteArrayPrefixOrZero`, `FIPS.lean:47–64`), and that layer is
unchanged.

The adapters needed are size lemmas. They are generic and **hash-specs should own them**:

```lean
-- Hash/Keccak/Properties.lean or API.lean, @[simp]
theorem Hash.Keccak.Reference.length_keccak (c : Nat) (hc : c < 1600) (N : List Bool) (d : Nat) :
    (keccak c N d).length = d
theorem Hash.shake128_size (m : ByteArray) (d : Nat) : (Hash.shake128 m d).size = d
theorem Hash.shake256_size (m : ByteArray) (d : Nat) : (Hash.shake256 m d).size = d
theorem Hash.sha3x224_size (m : ByteArray) : (Hash.sha3x224 m).size = 28   -- …256/384/512
theorem Hash.keccak256_size (m : ByteArray) : (Hash.keccak256 m).size = 32
-- Hash/SHA2/…, @[simp]
theorem Hash.sha224_size (m : ByteArray) : (Hash.sha224 m).size = 28
theorem Hash.sha256_size (m : ByteArray) : (Hash.sha256 m).size = 32
theorem Hash.sha384_size (m : ByteArray) : (Hash.sha384 m).size = 48
theorem Hash.sha512_size (m : ByteArray) : (Hash.sha512 m).size = 64
theorem Hash.sha512t224_size (m : ByteArray) : (Hash.sha512t224 m).size = 28
theorem Hash.sha512t256_size (m : ByteArray) : (Hash.sha512t256 m).size = 32
```

I proved `length_keccak`, `shake256_size` and `sha3x256_size` against our v4.35.0 build in a
scratch file, with no `sorry` and no warnings. Each is 4–8 lines and goes through `*_eq` +
`length_bytesToBitsLSB` + `Sponge.length_squeeze`/`length_absorb`/`le_blocks_mul`:

```lean
theorem length_keccak (c : Nat) (hc : c < 1600) (N : List Bool) (d : Nat) :
    (Keccak.Reference.keccak c N d).length = d := by
  unfold Keccak.Reference.keccak Sponge.sponge
  have hf : ∀ S, (Keccak.keccakP 6 24 S).length = 1600 := fun S => by
    rw [Keccak.length_keccakP 6 24 (by decide)]; rfl
  rw [List.length_take, Sponge.length_squeeze _ _ 1600 (by omega) hf _
    (Sponge.length_absorb _ 1600 _ hf _ List.length_replicate _)]
  have := Sponge.le_blocks_mul (r := 1600 - c) d (by omega)
  omega

theorem shake256_size (m : ByteArray) (d : Nat) : (Hash.shake256 m d).size = d := by
  have h := congrArg List.length (Hash.Keccak.shake256_eq m d)
  simp only [length_bytesToBitsLSB, Array.length_toList, ByteArray.size_data] at h
  rw [Keccak.Reference.shake256, length_keccak _ (by decide)] at h
  omega
```

The SHA-2 size lemmas would need a length lemma for `Hash.SHA2.Reference.hash`, which does not
exist yet. Either prove that from `take P.digestBits` plus an 8-word invariant, or prove the size
directly on `Fast.hashWith`. I did not attempt it; I estimate 10–20 lines.

Also useful in hash-specs: the prefix lemma in VCVio's orientation, to avoid `.symm` at every
use. This is optional.

```lean
theorem Hash.Keccak.take_shake256 (m : ByteArray) {d₁ d₂ : Nat} (h : d₁ ≤ d₂) :
    (Hash.shake256 m d₂).data.toList.take d₁ = (Hash.shake256 m d₁).data.toList
```

## 5. Proposed bridge theorems

VCVio's contribution policy is "full cutover, no backward-compatibility shims"
(`docs/agents/gotchas.md:295–298`, and the PR template checkbox "no deprecated aliases"). The
recommended path therefore **deletes** VCVio's SHA-2, SHA-3 and SHAKE bodies rather than
bridging to them. No `X.hash_eq` theorem is needed for the cutover. Executable agreement is
already established (§7), and the only proofs that see the bodies are re-proved from hash-specs
lemmas (§3.1).

Bridges become necessary only if maintainers want to keep `VCVio.Algorithms.Sha2` internals for
PR #910 (§8, risk R1). In that case:

```lean
-- in VCVio, e.g. VCVio/Algorithms/Sha2Bridge.lean
open VCVio.Algorithms in
theorem Sha2.bsig0_eq (x : UInt32) :
    Sha2.bsig0 x = Hash.SHA2.Fast.bigSigma Hash.SHA2.sha256.bigSigma0 x
-- likewise bsig1, ssig0, ssig1, ch, maj, and the 64-bit versions

theorem Sha2.compress_eq (st : Array UInt32) (m : ByteArray) (base : Nat) :
    Sha2.compress st m base =
      Hash.SHA2.Fast.compress Hash.SHA2.sha256
        ((Hash.SHA2.sha256.K.map Hash.SHA2.Fast.Word.ofNat).toArray) st m base

theorem Sha2.compress512_eq (st : Array UInt64) (m : ByteArray) (base : Nat) :
    Sha2.compress512 st m base =
      Hash.SHA2.Fast.compress Hash.SHA2.sha512
        ((Hash.SHA2.sha512.K.map Hash.SHA2.Fast.Word.ofNat).toArray) st m base

theorem Sha2.sha256_eq (m : ByteArray) : Sha2.sha256 m = Hash.sha256 m   -- and the other five
theorem Keccak.f1600_eq (s : Array UInt64) (hs : s.size = 25) :
    Keccak.f1600 s = Hash.Keccak.Fast.keccakF s
theorem Keccak.shake256_eq (m : ByteArray) (d : Nat) : Keccak.shake256 m d = Hash.shake256 m d
```

| Bridge | Difficulty | Why |
|---|---|---|
| `bsig0_eq` etc. | **easy** (`bv_decide`, or `UInt32.toBitVec_inj` + the hash-specs lemma `(UInt32.rotr x n.toUInt32).toBitVec = x.toBitVec.rotateRight n`, `Hash/Prelude/BytesLemmas.lean:170`) | VCVio's `rotr` is `(x >>> n) ||| (x <<< (32 - n))` |
| `compress_eq`, `compress512_eq` | **structural, medium** | VCVio uses `Id.run do for … [0:64]` with `set!`/`!`, while ours uses `List.foldl` with `getD`. It needs for-in to foldl conversion, schedule equality index by index, and `!` = `getD` (both default to 0). Executable agreement holds even for `st.size < 8` and reads past the end of `m` (§7), so it is likely unconditional. |
| `sha256_eq` etc. | **medium** | `compress_eq` plus `pad = Fast.pad` (VCVio uses `len.toUInt64 * 8`, we use `natToBytesBE 8 (8 * size)`; both keep the low 64 bits) and state serialisation |
| `f1600_eq` | **hard-ish** | VCVio indexes lanes through `piLUT`/`rhoLUT` tables, with `B'.set! piLUT[i]! …` in a fold. We use `tabulate` and `getD`. It needs 25-lane extensionality per step, per round. |
| `shake256_eq` | **medium given `f1600_eq`** | VCVio's padding (`absorb`, `Keccak.lean:71–83`) is the same byte-level pad10*1 as `Fast.pad`. Squeezing is `floor` full blocks plus a partial in VCVio, versus `ceil` blocks then `extract` in ours. |

## 6. Gaps in hash-specs

| ID | Gap | Needed by | Severity |
|---|---|---|---|
| **G1** | **HMAC (FIPS 198-1) over SHA-256/512 and MGF1 (RFC 8017 §B.2.1) over SHA-256/512.** Our ROADMAP lists HMAC only as a "cheap follow-on" (`ROADMAP.md:23`). | SLH-DSA-SHA2 `PRF_msg` and `H_msg` at all six SHA2 parameter sets (`FIPS.lean:163–183`), and the SHA2-128-24 instance (`Instance.lean:104–112`). | Blocks deleting `VCVio/Algorithms/Sha2.lean` entirely. It does not block adoption: VCVio can keep a ~30-line HMAC/MGF1 on top of `Hash.sha256/512`. I wrote that version in scratch and it matches VCVio's on 300+ lengths and all four HMAC and two MGF1 KATs (§7). |
| **G2** | `@[simp]` output-size lemmas for every byte-API function | `Prehash.digestRaw_size`, `ByteConformance.toList_byteArrayPrefixOrZero_shake256`, VCVio's "one-call simp" gate file | Blocks the cutover PR. Small (§4). |
| **G3** | **Performance bug:** `Hash.Keccak.Fast.squeeze` (`Hash/Keccak/Fast.lean:104–107`) evaluates `keccakF a` before recursing, including on the last block, where the result is discarded. Every `sponge` call therefore does `⌈d/r⌉` squeeze permutations instead of `⌈d/r⌉ − 1`. For one-block outputs (SHA-3, Keccak-256, the SHAKE calls in SLH-DSA) that is **2 permutations instead of 1**. `State.squeezeBytes` (`Stream.lean:65–69`) has the same problem. | SLH-DSA SHAKE KATs on VCVio's per-PR CI | Should land before VCVio's cutover. Interpreter measurements (§7): `Hash.shake256 m 16` costs 3550 µs against VCVio's 1376 µs (2.58×). Raw permutations cost 1753 µs against 1270 µs (1.38×). So about 2 of the 2.58× is the wasted permutation and the rest is per-permutation overhead. The compiled ratio is **unverified**. |
| G4 | No incremental XOF reader that can squeeze more output later from the same state | `Extern/Falcon/SamplerZ.lean:69–73`, whose PRNG `refill` re-squeezes from offset 0 each time (quadratic). Also ML-KEM SampleNTT and ML-DSA RejNTTPoly, which use fixed-length streams (840 and 4096 bytes) and panic if exhausted (`Extern/MLKEM/Instance.lean:59–74`, `Extern/MLDSA/Sampling.lean:76–92`). | Only matters if Extern moves off FFI. VCVio's FFI binding has the same one-shot shape today. |
| G5 | `USize` output length | `FFI.Hashing.shake*` takes `USize` | Trivial: `n.toNat` at call sites |

Hash-specs does **not** need the following, all of which VCVio's SLH-DSA reads as an EVM
convention and builds itself:

- Keccak-f over `Nat` lanes
- sponge-level APIs (VCVio only uses `shake*` at the byte level)
- C13's top-16-byte truncation (`top16`)
- C13's `toInt256`

## 7. Discrepancies

**No behavioural discrepancy was found.** All checks (kept in `evidence/vcvio/`) were run against the built
hash-specs `98c225d` via `lake env lean --run`. They used verbatim copies of
`VCVio/Algorithms/{Keccak,Sha2,Encoding}.lean`, with the `module`/`@[expose]` syntax stripped.

- **Differential test, 5,878 checks, 0 mismatches.** Message lengths 0–299, 511–513, 1000,
  1023–1025 and 4096. The checks compared:
  - `sha224/256/384/512` and `sha512Trunc224/256` against `Hash.sha224…sha512t256`
  - `sha3Digest*` against `Hash.sha3x*`
  - `keccak256` against `Hash.keccak256`
  - `shake128` and `shake256` at varied output lengths, plus output lengths 0, 1, 135–137,
    167–169, 272, 336, 337, 840 and 4096
  - the Prehash SHAKE expressions (`squeeze (absorb m 168 0x1f) 32` and
    `squeeze (absorb m 136 0x1f) 64`) against `Hash.shake128 m 32` and `Hash.shake256 m 64`
  - `hmacSha256/512` and `mgf1Sha256/512` against an HMAC/MGF1 rebuilt on `Hash.sha256/512`
- **VCVio's own KATs on hash-specs: PASS.** I ran the bodies of `testSha2`, `testHmacAndMgf` and
  `testShake` from `VCVioTest/Algorithms/Hash.lean:87–259`, with `Hash.*` substituted. That
  covers padding neighbours 55/56 and 111/112, exact-rate SHA-3 padding, SHAKE256 rate crossings
  135/136/137/272, a SHAKE128 200-byte multi-block squeeze, the 200-byte `0xa3` (1600-bit)
  absorb, and HMAC with long-key hash-then-pad. I did not run the JSON projection check, because
  it reads a file path relative to the VCVio root.
- **Internals:** VCVio `compress`/`compress512` equal `Hash.SHA2.Fast.compress` at
  `sha256`/`sha512` on 200 random (state, message, offset) triples. They also agree with an
  8-word state and an out-of-range offset, and with a 5-word state; both sides panic and read
  0. `bsig0`/`ssig1` equal `bigSigma`/`smallSigma`. `Sha2.k`/`k512` equal
  `K256`/`K512 .map ofNat`. `Keccak.f1600` equals `Hash.Keccak.Fast.keccakF` on 50 random
  states.
- **Length-field wrap:** VCVio `Sha2.pad` computes `len.toUInt64 * 8` (`Sha2.lean:110`), which
  wraps at 2^61 bytes. Ours keeps the low `lengthBits` of `8 * m.size`. These are the same
  function. VCVio's `sha256Checked` rejects that domain explicitly.

Issues I found that are not discrepancies between the two libraries:

- **hash-specs (G3):** the wasted final permutation in `Fast.squeeze`.
- **hash-specs ROADMAP §1:** it lists `VCVio/HashSig/SLHDSA/Concrete/Keccak.lean` and
  `Sha2.lean`. These have moved to `VCVio/Algorithms/Keccak.lean` and `Sha2.lean`.
- **VCVio, already tracked:** `sha2Thash` (`FIPS.lean:262–275`) computes a singleton `T_ℓ` at
  `n ∈ {24, 32}` with SHA-256 and `64−n` padding, where FIPS 205 §11.2.2 prescribes SHA-512 and
  `128−n`. This is documented as unreachable and tracked in open issue #629, item 1. It is not
  a hash-specs concern.
- **VCVio, outside FIPS:** ML-KEM `concreteSampleNTT` squeezes a fixed 840 bytes and panics if
  rejection sampling under-fills (`Extern/MLKEM/Instance.lean:59–74`). FIPS 203 Algorithm 7 is
  an unbounded XOF loop, so this is a (negligible-probability) deviation outside FIPS. ML-DSA
  `rejNTTPoly` uses 4096 bytes (`Extern/MLDSA/Sampling.lean:91–92`). Falcon's PRNG refill is
  quadratic (`SamplerZ.lean:69–73`).
- **Unverified:** that VCVio's FFI SHA-3 agrees with hash-specs. I did not build the C backend.
  A differential test belongs on VCVio's nightly path (PR V4).

## 8. PR plan

Conventions:

- **VCVio:** PR titles are either conventional (`feat(HashSig): …`, `refactor(Quantum): …`,
  `chore: …`, `docs(…): …`) or plain sentences (#912, #913, #914, #917). PRs go through a merge
  queue, and stacked PRs need the async merge API (`CONTRIBUTING.md`, "Pull Request Checks And
  Merge Queue").
- **VCVio requirements:**
  - the PR template's Summary, Verification and Checklist sections
  - the standard file header
  - plain `public section` plus per-declaration `@[expose]` in new files, with the expose
    baseline not raised
  - `./scripts/update-lib.sh`
  - `lake exe axiomsweep --check`, with the baseline untouched. Our theorems use only `propext`,
    `Classical.choice` and `Quot.sound` (`HashTests/Axioms.lean`), so it is unaffected.
  - no linter suppression
  - **no deprecated aliases or shims**
  - **no AI-attribution line** (`AGENTS.md:26`, `CONTRIBUTING.md` "AI assistance")
- **No CODEOWNERS file** (`.github/` has none).
- **hash-specs:** conventional titles (`feat(…)`, `build:`, `perf`-style).

**Open PRs and issues that touch this area** (searched with `gh pr list`/`gh issue list -R
Verified-zkEVM/VCVio` for keccak, sha2, shake, sha3, hmac, Algorithms and FFI):

- **#910** (draft, "feat(Cryptol): Foundation and VCVio bridges…"):
  - imports `VCVio.Algorithms.Sha2` and `Keccak`
  - proves `foundationSigma_eq : foundationSigma x = VCVio.Algorithms.Sha2.bsig0 x`
  - uses `Sha2.compress`, `RoundState`, `iv`, `k`, and `Keccak.sha3Digest*`/`shake*`/`keccak256`
    in `Interop/Cryptol/Bridge/{CLI,HashCLI,Correspondence,Specifications,Round,…}.lean`
  - adds `VCVio.Algorithms.CRC`
- **#879** (issue): Cryptol coordination, same area.
- **#629** (issue): SLH-DSA follow-ups, including the `F`/`T₁` item above. Item 3 says extending
  the wire-tamper test to all 12 profiles is "cheap once runtime allows". That is further
  evidence that runtime matters.
- **#508, #849, #471**: they touch HashSig, ML-DSA or Falcon but no hash files (their file lists
  have no `Algorithms/`, `Hashing` or `lakefile`).

### Prerequisites in hash-specs

| # | Title | Files | Size | Notes |
|---|---|---|---|---|
| H1 | `feat: output-size simp lemmas for the byte API` | `Hash/Keccak/Properties.lean` (`length_keccak`), `Hash/Keccak/Equiv.lean` or a new `Hash/Keccak/APILemmas.lean`, `Hash/SHA2/…`, `HashTests/Axioms.lean` | S (~80 lines) | §4. The Keccak half is already proved in scratch. |
| H2 | `perf(Keccak): drop the trailing permutation in the fast squeeze` | `Hash/Keccak/Fast.lean:104–107`, `Hash/Keccak/Stream.lean:65–69`, `Equiv.lean` and `StreamLemmas.lean` proofs that unfold `squeeze` | S–M | For example, emit `rateBytes` and permute only when `k > 0`. Re-run `harness/` benchmarks, where 64-byte Keccak-256 should roughly double. Strongly recommended before V2. |
| H3 | `feat(SHA2): HMAC (FIPS 198-1) and MGF1 (RFC 8017)` | new `Hash/SHA2/HMAC.lean`, `MGF1.lean`, `API.lean` (`Hash.hmacSha256`, `hmacSha512`, `mgf1Sha256`, `mgf1Sha512`), KATs (RFC 4231; VCVio's four HMAC and two MGF1 cases) | M | A generic `hmac (H : ByteArray → ByteArray) (B : Nat)` is enough. A reference/bit-level counterpart is optional. Unblocks V3. |
| H4 | (optional) `feat(Keccak): incremental XOF reader` | `Hash/Keccak/Stream.lean` | M | Only for V4b |

Then cut a release, `v4.35.0-patch2` (or whatever VCVio's toolchain is at the time), since
VCVio should pin a tag.

### PRs to VCVio

| # | Title | Files | Lakefile | Deleted / kept | Proof rework | Size | Risks |
|---|---|---|---|---|---|---|---|
| V1 | `build: require hash-specs` | `lakefile.lean`, `lake-manifest.json`, `scripts/CheckImports.lean:45–47` (add `"Hash"` to the `VCVio.Algorithms` whitelist, needed only if Algorithms imports it), `docs/design/repository-layout.md:11, 76–82`; plus a regression in `VCVioTest/Algorithms/Hash.lean` that runs every KAT on **both** implementations | Insert **before** the Mathlib line, as the comment at `:68–72` requires for PolyFun: `require «hash-specs» from git "https://github.com/Verified-zkEVM/hash-specs" @ "v4.35.0-patch1"` | nothing deleted | none | S | The downstream-consumer CI job (`build.yml:129ff`) fetches our release oleans. `fixedToolchain` ties future VCVio bumps to our tags. Package name with a hyphen needs `«»` in the DSL. |
| V2 | `refactor(HashSig): take SHA-2, SHA-3 and SHAKE from hash-specs` | the §3.2 files (`Concrete/{FIPS,Instance,Prehash}.lean`, `C13/Concrete.lean`, `Security/ByteConformance.lean`, `HashSigTest/SLHDSA/{ByteModel,PrimitiveTests}.lean`, `VCVioTest/Algorithms/Hash.lean`); **delete** `VCVio/Algorithms/Keccak.lean` and `KeccakPrefix.lean`; **shrink** `VCVio/Algorithms/Sha2.lean` to HMAC/MGF1 and the checked wrappers over `Hash.sha256/512`; `VCVio.lean` umbrella; the docs in §3.2; `scripts/InitSweep.lean:186` and fixture docstrings | none | Delete about 280 lines (Keccak 170, KeccakPrefix 108, and the SHA-2 core in `Sha2.lean:32–181, 211–355`). Keep `Encoding.lean`. | `ByteConformance.lean:110–143, 205`; `Prehash.lean:143–145` (needs H1); `VCVioTest/Algorithms/Hash.lean:33–43` | M (about 300 lines changed) | **R1:** breaks #910 if #910 lands first; if V2 lands first, #910 must retarget to `Hash.SHA2.Fast` (its `foundationSigma_eq` proof gets *easier* with our `rotr` lemma). **R2:** CI runtime of `slhdsa_byte_model_tests` and the other SHAKE tests, so land H2 first and compare `lake test` wall time before and after. **R3:** "one-call simp" gate: `digestRaw_size` must still close with one `simp`, so the H1 lemmas must be `@[simp]`. |
| V3 | `refactor(HashSig): take HMAC and MGF1 from hash-specs` | `FIPS.lean:163–183`, `Instance.lean:104–112`; delete the rest of `VCVio/Algorithms/Sha2.lean` (move `*Checked` and `InputError` into the test, their only user); revert the `CheckImports` whitelist if nothing in Algorithms imports `Hash` | none | the remaining `Sha2.lean` | none | S | needs H3 |
| V4a | `test(Extern): differential check of FFI SHA-3 against hash-specs` | new `LatticeCryptoTest/Hashing/Agreement.lean`, plus a step in `lakefile.lean:427–428` | add a `lean_exe` | none | none | S | nightly only. This verifies the FFI binding (currently **unverified**). |
| V4b (optional, maintainers' call) | `refactor(Extern): back FFI.Hashing with hash-specs` | `Extern/Hashing.lean`, `Extern/MLKEM/FFI.lean:34–43`, call sites in §3.3; drop `hashing_ffi.o` and `extern_lib leanhashing` (`lakefile.lean:166–185`) and `csrc/hashing/` | remove `leanhashing` | removes C hashing from the TCB of the Lean-side ML-KEM, ML-DSA and Falcon | none (opaque today) | S–M | **Performance:** ML-DSA ExpandA squeezes 4096 bytes per matrix entry (up to 56 entries), and Falcon's refill is quadratic, so pure Lean could slow the nightly noticeably. Our compiled Keccak is ~350× slower than C (`harness/BENCHMARKS.md`, Keccak-256 table). **Recommend keeping the FFI** (it is nightly-only and paired with C reference backends anyway) and doing V4a instead. |

## 9. Open questions for the maintainers

1. **Cutover vs coexistence.** The policy forbids shims, so V2 deletes `VCVio.Algorithms.Keccak`
   and the SHA-2 core outright. Is that acceptable while #910 depends on `Sha2.compress`,
   `round256` and `bsig0`? Alternatively, should #910 retarget to `Hash.SHA2.Fast.compress` and
   `bigSigma`, which are also `Array`-based with `getD`?
2. **HMAC and MGF1:** keep them in VCVio (on `Hash.sha256/512`), or wait for H3? Is a byte-level
   definition enough, or do you want a reference (bit-level) counterpart with an `Equiv` proof?
3. **The Algorithms layering rule** (`scripts/CheckImports.lean:45–47`): may
   `VCVio/Algorithms/*` import `Hash`, or should the HMAC/MGF1 residue move under
   `HashSig/SLHDSA/Concrete`?
4. **Runtime budget:** what is the acceptable wall time for `lake test`, and specifically for
   `slhdsa_byte_model_tests`? This decides whether H2 must land first and whether more profiles
   (#629 item 3) become affordable.
5. **FFI:** keep `FFI.Hashing` (nightly, C-speed) and only add V4a, or move Extern to pure Lean
   to shrink the native TCB?
6. **Release cadence:** VCVio bumps toolchain and PolyFun often. Is a hash-specs release tag per
   Lean minor (as CompPoly does) enough, or do you want us to track nightlies or RCs?
