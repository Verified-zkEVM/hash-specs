# Upstreaming record: `evm-asm` (and `riscv-zkvm`)

Recorded 2026-10-27 against hash-specs `98c225d`. All file:line references are to the commits below. Claims not checked against source are marked **unverified**.

## 1. Snapshot

| | evm-asm | riscv-zkvm (dependency) |
|---|---|---|
| Repo | `Verified-zkEVM/evm-asm` | `Verified-zkEVM/riscv-zkvm` |
| Commit examined | `7e65e4d` (HEAD, committed 2026-09-04) | `6810fc1` (HEAD, 2026-10-06); evm-asm pins tag **`v0.3.0`** = `afcbc45` (`lakefile.toml`, `lake-manifest.json`) |
| Toolchain | `leanprover/lean4:v4.33.0` | HEAD `v4.33.1` (tag `v0.4.0`); `v0.3.0` was `v4.33.0` |
| Mathlib | `v4.33.0` (rev `db584cd`) | none: `RiscvZkvm.Rv64` is Mathlib-free (lakefile comment "no Sail and no Mathlib dependency") |
| Other pins | `riscv-zkvm` `v0.3.0`, Sail `8d57a8b`, Cli `v4.33.0` | Sail (lean-sail) only |
| Module system | mixed: 1850 of 3103 `EvmAsm/**/*.lean` start with `module`. The hash-bridge proofs (`Codegen/Proofs/HashBridge*.lean`, `Rv64/SAsm/KeccakStep.lean`) are **not** modules; `Stateless/SpecRef/*.lean` are. | modules throughout |
| Lakefile | `lakefile.toml`, `preferReleaseBuild`, prebuilt-olean releases | `lakefile.toml`, `fixedToolchain = true` |

**Toolchain gap.** evm-asm is at v4.33.0, two minor versions behind hash-specs (v4.35.0). hash-specs sets `fixedToolchain = true`, and a `require` at a different toolchain does not work. There are two options:

- **(a) Cut a hash-specs release at `v4.33.0`. Recommended.** It covers only the core package, built against Mathlib `v4.33.0` with the same rev (`db584cd`) as evm-asm. evm-asm already requires Mathlib, so the core package adds no new transitive dependency. **Verified 2026-10-27:** the core (`Hash`, `HashTests`) at `98c225d` builds unchanged on v4.33.0 with Mathlib `v4.33.0` (= `db584cd`), with 0 warnings. Effort: S. The zk package is not needed by evm-asm and can be skipped for this tag.
- **(b) Bump evm-asm to v4.35.0. Not realistic now.**
  - It needs a riscv-zkvm release at v4.35. riscv-zkvm PR #19 ("refresh Lean 4.35 and official lean-sail v7") is a **draft, paused at the maintainer's request on 2026-10-22**, with no v0.5.0 tag.
  - It needs a Mathlib bump across about 3100 files, including about 28.8k lines of hash-bridge proofs.
  - Open issue #12755 already reports v4.33 elaboration memory problems.
  - The last bump (PR #12731, "chore: bump to Lean v4.33.0 …") was a dedicated effort.
- If evm-asm moves to riscv-zkvm `v0.4.0` (v4.33.1; PR #17 "hold v0.4.0 pending upstream cache fix"), the hash-specs release would have to be `v4.33.1` instead.

**Project status.** README.md (lines 3–7, PR #13263, merged 2026-09-04) says: "Project direction is under reconsideration … contributions to evm.asm may not ultimately be used". Issue #13264 (2026-10-22) compares against the Pancake guest. Any upstreaming here should therefore be cheap and incremental.

## 2. Overlap inventory

Four layers. Only layers A, B and D define hash functions. Layer C proofs use B as their *target*. Layer E is an abstract interface.

### A. Concrete accelerator semantics (`riscv-zkvm`; evm-asm only re-exports them)

These are **not** axiomatised. Each `csrs <id>, rs1` instruction is given a concrete Lean function (`ZiskAccel.lean:1-58`, rationale at 15-23: "an axiomatized accelerator contract would widen [the trusted base]"). They are what ZisK's `Keccakf`/`Sha256f`/`Blake2bRound` precompiles are *assumed* to compute. evm-asm's `EvmAsm/Rv64/ZiskAccel.lean:84-101` is a generated `export` shim (`scripts/gen-rv64-shims.py`): `EvmAsm.Rv64.Accel.keccakF` *is* `RiscvZkvm.Rv64.Accel.keccakF`, so there is no duplication. The file is byte-identical at `v0.3.0` and HEAD `6810fc1` (diffed via `gh api`).

| riscv-zkvm `RiscvZkvm/Rv64/ZiskAccel.lean` | Signature / representation | hash-specs counterpart |
|---|---|---|
| `:76` `Accel.keccakRC` | `List (BitVec 64)` | `Hash.Keccak.Fast.roundConstantWords` (`Array UInt64`) |
| `:87` `Accel.rhoOff` | `Nat → Nat → Nat` (table) | rho offsets in `Hash/Keccak/Fast.lean` (`rho`) |
| `:97` `Accel.keccakRound` | `BitVec 64 → List (BitVec 64) → List (BitVec 64)`; lane (x,y) at `x+5y`; reads use `getD 0`; output is always 25 lanes (`List.ofFn`) | `Hash.Keccak.Fast.round : Array UInt64 → Nat → Array UInt64` |
| `:113` `Accel.keccakF` | `List (BitVec 64) → List (BitVec 64)`, 24 rounds | `Hash.Keccak.Fast.keccakF : Array UInt64 → Array UInt64` (`Fast.lean:81`); `Equiv.toState_keccakF` ties it to the bit-level reference |
| `:165,199` `keccakF_kat_empty`, `keccakF_kat_rlp_empty` | kernel `decide` KATs | none needed |
| `:235` `sha256K`, `:254` `sha256W` | `List (BitVec 32)` | `SHA2.Reference.schedule SHA2.sha256` (`Reference.lean:129`) |
| `:266` `Accel.sha256Compress` | `(hs w : List (BitVec 32)) → List (BitVec 32)`; uses `hs.take 8` and `zipWith`, so it returns `< 8` words if `hs.length < 8` | `Hash.SHA2.Reference.compress Hash.SHA2.sha256` (`Reference.lean:164`, `List (BitVec sha256.w)`, always 8 words) |
| `:321` `blake2Sigma` | `List (List Nat)` | `Hash.BLAKE2.SIGMA` |
| `:335` `blakeG` | `List (BitVec 64) → Nat⁴ → BitVec 64² → List (BitVec 64)` | `Hash.BLAKE2.Reference.G blake2bParams` (`Reference.lean:78`) |
| `:352` `Accel.blake2bRound` | `(idx : Nat) (v m : List (BitVec 64))`; note the argument order | `Hash.BLAKE2.Reference.round blake2bParams m v i` (`Reference.lean:92`) |
| `:550-581` `dwordsToU32s`, `dwordsToU32sBE`, `u32sToDwords`, `byteSwap32` | ZisK LE-u32-in-u64 packing of the Sha256f operand | none; machine-specific, stays in riscv-zkvm |
| `:703-786` `MachineState.csrsWrite`/`execCsrs`/`csrsValid` | CSR 0x800 Keccakf (25 LE lanes in place), 0x805 Sha256f (`[state*, input*]`), 0x819 Blake2bRound (`[idx, state*, input*]`, `idx < 10` checked at `:871`) | none; machine semantics |

### B. Full-message SpecRef hashes (evm-asm `EvmAsm/Stateless/SpecRef/Crypto.lean`, built on A)

Bytes are `List (BitVec 8)` (`:34-38`).

| Location | Name | Representation | Replacement |
|---|---|---|---|
| `:44,50,60` | `bytesLEtoNat`, `natToBytesLE`, `natToBytesBE` | `List (BitVec 8)` ↔ `Nat` | generic helpers; keep |
| `:69-76` | `chunkBytes` | fuel-based chunking | keep |
| `:81` | `keccakRateBytes := 136` | | |
| `:86` | `keccakPad` | pad10*1 with domain byte 0x01; `0x81` if one byte remains | `Hash.Keccak.Fast.pad 136 0x01` |
| `:95` | `keccakAbsorbBlock` | 17 LE lanes XOR into 25 `BitVec 64` | `Fast.absorbBlock` (which includes `keccakF`) |
| `:103` | `keccakAbsorb` | fold `Accel.keccakF ∘ absorbBlock` | `Fast.sponge` (absorb part) |
| `:109` | **`keccak256 : Bytes → Bytes`** | first 4 lanes, LE | **`Hash.keccak256 : ByteArray → ByteArray`** (`Keccak/API.lean:46`) |
| `:142` | `sha256IV` | `List (BitVec 32)` | `SHA2.Reference.initialHash SHA2.sha256` |
| `:148` | `sha256Pad` | 0x80, zeros, 64-bit BE length | `SHA2.Reference.pad` (bit-level) |
| `:155` | `sha256BlockWords` | 16 BE words | `SHA2.Reference.parse` |
| `:160` | `sha256Compress'` | fold of `Accel.sha256Compress` | `MerkleDamgard.iterate (compress P)` |
| `:166` | **`sha256 : Bytes → Bytes`** | | **`Hash.sha256`** (`SHA2/API.lean:30`) |
| `:171` | `sha256Pair a b := sha256 (a ++ b)` | SSZ | `Hash.sha256 (a ++ b)` |
| `:249-262` | `#guard` KATs: keccak256 of "" and "abc", sha256 of "" and "abc" | compiled evaluation | |

### C. Proof-only byte/state views for the guest Keccak and SHA-256 routines (evm-asm)

These are *operational* digests, proved equal to B. They are not specs in their own right.

| Location | Name | Notes |
|---|---|---|
| `Rv64/SAsm/KeccakStep.lean:16,20` | `keccakDwords`, `keccakBytes` | 200-byte window ↔ 25 LE dwords around `Accel.keccakF` |
| `Rv64/SAsm/AccelStep.lean:1986,1999` | `sha256Dwords`, `sha256Bytes` | Sha256f operand window around `Accel.sha256Compress` |
| `Codegen/Proofs/HashBridgeKeccakSpec.lean:49-67` | `keccakAbsorbBlocks`, `keccakStateBytes`, `keccakAbsorbedState`, fuel functions | |
| `Codegen/Proofs/HashBridgeKeccakPure.lean:77,90` | `keccakSqueeze32`, `keccakGuestPad` | |
| `Codegen/Proofs/HashBridgeKeccakBody.lean:362,368` | `keccakBodyPrePad`, `keccakBodyDigest` | |
| `Codegen/Proofs/HashBridgeSha256Body.lean:57-117` | `sha256IvBytes`, `sha256BodyFinalState`, `sha256BodyDigest` | |
| `Codegen/Proofs/HashBridgeSha256OuterBody.lean:119,157`, `HashBridgeSha256Squeeze.lean:203` | `sha256CompressBytes`, `sha256AbsorbedState`, `sha256SqueezeBE` | |

No hash-specs counterpart is needed for these; they stay.

### D. EVM precompile specs (evm-asm `EvmAsm/Stateless/SpecRef/PrecompilesHash.lean`)

These are ported from execution-specs `@tests-zkevm@v0.5.0`, `bd8c673` (`:4-16`). The words are **unbounded `Nat`**, with `% 2^32` and `% 2^64` applied by hand.

| Location | Name | Representation | Replacement |
|---|---|---|---|
| `:36-145` | `Ripemd160.{f,K,K',r,r',s,s',compressBlock,hash}` | `List Nat` words, `Bytes` in and out (20 bytes) | **no counterpart (gap)** |
| `:149` | `pRipemd160 : EvmM Unit` | gas, then 12 zero bytes ++ digest | keep (EVM-specific wrapper) |
| `:159-216` | `Blake2b.{IV,sigma,mixTable,rotr,G,compress}` | `compress (num_rounds) (h m : List Nat) (t0 t1 : Nat) (f : Bool) : Bytes` | `Hash.blake2bF` (`BLAKE2/API.lean:47`) plus LE serialisation |
| `:219` | `Blake2b.leWords` | 64-bit LE words from bytes | `ByteArray.getUInt64LE` |
| `:226` | `pBlake2f : EvmM Unit` | length 213, rounds BE, gas, `f ∈ {0,1}` | `Hash.blake2bPrecompile` (`BLAKE2/API.lean:54`) for the output; gas stays |
| `:243-255` | `#guard` KATs | RIPEMD-160 of "" and "abc"; BLAKE2b-512("abc") from RFC 7693 Appendix A | |
| `SpecRef/Precompiles.lean:81-86` | `pSha256` | uses B's `sha256` | `Hash.sha256` |

### E. Abstract or interface-only surfaces (no hash computation)

- `EL/KeccakEcallBridge.lean:77` `executeKeccakEcall (accelerator : AcceleratorInput → AcceleratorOutput)` takes the hash as a **parameter**. It is the ECALL 0x100 `zkvm_keccak256` C-ABI surface. Its only instantiation is a stub in `EL/Conformance/KeccakStackExecution.lean:34` (`vectorAccelerator` returns 0x00…/0xff…). A natural target for `Hash.keccak256` later, but nothing to replace now.
- `Evm64/Accelerators/Types.lean:83-89,160-166`: byte-array aliases (`ZkvmKeccak256Hash`, `ZkvmBlake2fState`, …).
- `Evm64/Accelerators/SyscallIds.lean:46,57,60,75`: syscall ids (keccak256 0x100, sha256 0x103, ripemd160 0x104, blake2f 0x109).
- `Evm64/Accelerators/Dispatch.lean:84`: `dispatch _ = .efail`, a skeleton.
- `SLHDSA/Primitives.lean:53-77`: `structure Primitives (p : Params)` bundles the opaque FIPS 205 functions `F`, `H`, `Tl`, `PRF`, `PRFmsg` and `Hmsg`. The only instance is `SLHDSA/DemoInstance.lean`, a non-cryptographic `mix h x := h + x` (`:41`). It has no SHA-2 or SHAKE instance, so it has no counterpart today. A hash-specs `shake256` instance would be the natural concrete layer later (§6).
- No `axiom` declarations about hashes anywhere in `EvmAsm/`. The trusted base is the three classical axioms (CONTRIBUTING.md). hash-specs' `keccak256_eq`, `sha256_eq`, `blake2bF_eq` and `toState_keccakF` also depend only on `[propext, Classical.choice, Quot.sound]` (checked with `#print axioms`), so adopting them does not widen evm-asm's trusted base.

**Software guest kernels** (RISC-V asm strings, not Lean specs): `Codegen/Programs/Ripemd160.lean` (376 lines, software, no ZisK accelerator, **no proof**), `Codegen/Programs/Blake2f.lean` (290 lines, F loop over `csrs 0x819`, **no proof**), and `Codegen/Programs/KeccakIncremental.lean`. `scripts/spike/zisk_accel.cc` is a separate C++ accelerator model for the Spike simulator.

## 3. How it is used

| Spec | Role | Consumers |
|---|---|---|
| `Accel.keccakF` | target and semantics | `KeccakStep.lean` (CSR step spec), `HashBridgeKeccakBridge.lean:376,731,856`, `HashBridgeKeccakSpec.lean`, and `AccountDecodeSpec.lean:449-470`, which proves `keccak256 [] = EMPTY_CODE_HASH` and `keccak256 [0x80] = EMPTY_TRIE_ROOT` by **kernel `decide` through `Accel.keccakF_kat_*`**. Seven files in total. |
| `Accel.sha256Compress`, `dwordsToU32s*` | semantics | `AccelStep.lean`, `HashBridgeSha256OuterBody.lean`, `HashBridgeSha256Top.lean`, `HashBridgeSha256Body.lean`. Five files. |
| `Accel.blake2bRound` | semantics only | referenced only via `execCsrs`. No Lean proof uses it (the Blake2f guest is unproved). |
| `SpecRef.keccak256` | **proof target** | The main bridges are `keccakBodyDigest_eq_specref` (`HashBridgeKeccakBridge.lean:1545`), `zkvm_keccak256_spec_within(_envelope)` (`HashBridgeKeccakTop.lean:301,408`), and `kssDigest_eq_specref` (`HashBridgeKeccakSegTop.lean:78`, only for `msg.length ≤ 135`). These are 22 files and about 18.0k lines. It also appears in the posts of about 20 `Codegen/Programs/*Spec*.lean` routine specs (`ValidateParentHashLinkSpec`, `BlockHashFromHeaderSpec`, `TxSigningHash*`, `AccountDecode*`, `NodeDb*`, `WitnessLookupByHashIndexedSpec`, …) and in `Evm64/Mpt{Assertions,Correspondence}.lean` and `Progress/*.lean`. In all, 46 files apply `keccak256` from SpecRef. |
| `SpecRef.keccak256` | executable | about 20 `Stateless/SpecRef/*.lean` files (the SpecRef interpreter: MPT, blocks, transactions, state tracker, …), the `specref-eest-check` executable, and the `#guard`s (`WitnessReads.lean:238`, `Crypto.lean:249,261`) |
| `SpecRef.sha256`/`sha256Pair` | **proof target** | `sha256BodyDigest_eq_specref` (`HashBridgeSha256Top.lean:1651`). The SHA-256 bridge is 11 files and about 10.7k lines. Downstream are `ExecutionRequestsHash*` and `RequestsHashParams`. In all, 16 files apply `sha256`. |
| `SpecRef.sha256` | executable | `pSha256`, `SszCodec.lean:280` (`zeroHash`), `PrecompilesKzg`, `SeamShell` |
| `Ripemd160.hash`, `Blake2b.compress` | executable only | `pRipemd160`/`pBlake2f` → `PrecompilesTable.lean:30,36`, plus the `#guard`s. No proof uses them. |

**Call sites that change** under the recommended "bridge, keep the definitions" plan: none. New files only.

Replacing the definitions (§8, PR E-6) would change:

- 2 executable call sites for RIPEMD-160 and BLAKE2F (`PrecompilesHash.lean:154,238`).
- Possibly `pSha256` (1 site).

Definitional replacement of `SpecRef.keccak256`/`sha256` is **not** recommended. The 28.8k lines of HashBridge proofs unfold these definitions (`keccak256_eq_squeeze_absorb := rfl`, `HashBridgeKeccakPure.lean:80-86`). The `decide` KATs need the kernel-reducible `List`-based `Accel.keccakF`, and kernel evaluation of `Hash.Keccak.Fast.keccakF` on `Array UInt64` is untested (**unverified**).

## 4. Representation gaps and adapter lemmas

| Gap | Adapter (Lean statement) | Who provides |
|---|---|---|
| `List (BitVec 8)` ↔ `ByteArray` | `def Hash.ByteArray.ofBVs (l : List (BitVec 8)) : ByteArray := ⟨(l.map UInt8.ofBitVec).toArray⟩`, `def ByteArray.toBVs (b : ByteArray) : List (BitVec 8) := b.data.toList.map UInt8.toBitVec`, plus `toBVs_ofBVs : (ofBVs l).toBVs = l`, `size_ofBVs`, `ofBVs_append` | **hash-specs** (generic, also useful for leanerVM and clean) |
| `List (BitVec 64)` lanes ↔ `Array UInt64` | `lanesOf (st : List (BitVec 64)) : Array UInt64 := (st.map UInt64.ofBitVec).toArray`, plus `(lanesOf st).toList.map UInt64.toBitVec = st` | **hash-specs** |
| byte-list sponge view | `theorem Hash.keccak256_toBVs (m : List (BitVec 8)) : (Hash.keccak256 (ofBVs m)).toBVs = <list-level sponge over Fast.keccakF>`, i.e. a `List`-based restatement of `Fast.sponge` with `getUInt64LE` ↔ `bytesLEtoNat` | **hash-specs** (generic; it removes most of the work in bridge B2) |
| `BitVec sha256.w` / `BitVec blake2bParams.w` vs `BitVec 32/64` | `@[simp] theorem SHA2.sha256_w : SHA2.sha256.w = 32 := rfl`, `@[simp] theorem BLAKE2.blake2bParams_w : blake2bParams.w = 64 := rfl`, plus specialised `BitVec 64` wrappers of `Reference.G/round/F` (and `BitVec 32` ones for `compress sha256`) | **hash-specs**. Both `rfl`s hold (checked), but see §7: unfolding `blake2bParams` inside `simp` leaves ill-typed `HAdd (BitVec blake2bParams.w)` instances. |
| ZisK Sha256f u32-in-u64 packing | `dwordsToU32s`, `dwordsToU32sBE` (riscv-zkvm) | stays in riscv-zkvm/evm-asm |
| `Nat` words (SpecRef BLAKE2/RIPEMD) ↔ `UInt64`/`BitVec` | `∀ x ∈ h, x < 2^64` side conditions; `Nat.toUInt64`, `BitVec.ofNat 64` | evm-asm (bridge-local) |

## 5. Proposed bridge theorems (in evm-asm)

They live in evm-asm, not riscv-zkvm, because riscv-zkvm is Mathlib-free (§10). Names were checked in both sources. `open EvmAsm.Rv64 EvmAsm.Stateless.SpecRef` is assumed.

```lean
-- A1. Keccak-f[1600] lane level. Holds for every input length (both sides read lanes with getD 0
--     and always output 25 lanes; checked numerically for lengths 0, 1, 24, 25, 26, 30).
theorem Accel.keccakF_eq_hashSpecs (st : List (BitVec 64)) :
    Accel.keccakF st =
      (Hash.Keccak.Fast.keccakF (st.map UInt64.ofBitVec).toArray).toList.map UInt64.toBitVec

-- A2. SHA-256 compression (needs 8 ≤ hs.length: Accel truncates via take 8/zipWith).
theorem Accel.sha256Compress_eq_hashSpecs (hs w : List (BitVec 32)) (h : 8 ≤ hs.length) :
    Accel.sha256Compress hs w = Hash.SHA2.Reference.compress Hash.SHA2.sha256 hs w

-- A3. BLAKE2b round (argument order differs).
theorem Accel.blake2bRound_eq_hashSpecs (i : Nat) (v m : List (BitVec 64)) (hv : v.length = 16) :
    Accel.blake2bRound i v m = Hash.BLAKE2.Reference.round Hash.BLAKE2.blake2bParams m v i

-- B1/B2. Full-message hashes.
theorem keccak256_eq_hashSpecs (m : Bytes) :
    keccak256 m = (Hash.keccak256 ⟨(m.map UInt8.ofBitVec).toArray⟩).data.toList.map UInt8.toBitVec
theorem sha256_eq_hashSpecs (m : Bytes) :
    sha256 m = (Hash.sha256 ⟨(m.map UInt8.ofBitVec).toArray⟩).data.toList.map UInt8.toBitVec

-- D1. EIP-152 F on Nat words.
theorem Blake2b.compress_eq_hashSpecs (rounds : Nat) (h m : List Nat) (t0 t1 : Nat) (f : Bool)
    (hh : h.length = 8) (hm : m.length = 16) (hhb : ∀ x ∈ h, x < 2^64) (hmb : ∀ x ∈ m, x < 2^64)
    (ht0 : t0 < 2^64) (ht1 : t1 < 2^64) :
    Blake2b.compress rounds h m t0 t1 f =
      (Hash.blake2bF rounds (h.map Nat.toUInt64).toArray (m.map Nat.toUInt64).toArray
        t0.toUInt64 t1.toUInt64 f).toList.flatMap (fun w => natToBytesLE 8 w.toNat)

-- D2 (after hash-specs gains RIPEMD-160).
theorem Ripemd160.hash_eq_hashSpecs (m : Bytes) :
    Ripemd160.hash m = (Hash.ripemd160 ⟨(m.map UInt8.ofBitVec).toArray⟩).data.toList.map UInt8.toBitVec
```

| Bridge | Difficulty | Why |
|---|---|---|
| A1 | structural, M (≈200–400 lines) | Same lane indexing (`x+5y`) and the same π source `(x+3y, x)` on both sides (`ZiskAccel.lean:102-105` vs `Fast.pi`). Prove round by round with per-lane `UInt64`/`BitVec 64` lemmas (`toBitVec_xor/and/not/rotateLeft`), 25 lanes, and a `decide`d equality for `rhoOff` and the round constants. Could instead go through `Equiv.toState_keccakF` to the bit-level reference, but that is longer. |
| A2 | structural, S–M | `schedule` and `sha256W` have the same `getD` shape, but the σ-sum order differs (`W[t-16] + s0 + W[t-7] + s1` vs `σ1 + W[t-7] + σ0 + W[t-16]`), so it needs `BitVec` add-comm/assoc. `K` is a `decide` on constant lists. evm-asm forbids `bv_decide`/`native_decide`; `bv_omega`, `ac_rfl` and `simp` are allowed. |
| A3 | structural, S | `blakeG` sets all four words at the end, while `Reference.G` sets them in sequence; they are equal for distinct in-range indices. I tried a `getD`/`set` proof in scratch (`evidence/evm-asm/Proof.lean`). It got stuck on the `BitVec blake2bParams.w` typing (§7), not on the mathematics. |
| B1 | hard, L (≈600–1500 lines) without the adapter, M with the §4 byte-list sponge view | It relates `chunkBytes`/`keccakPad`/`keccakAbsorbBlock`/`bytesLEtoNat` to `Fast.pad`/`absorbBlock`/`getUInt64LE` on `ByteArray` offsets, uses A1, and needs the squeeze of the first 4 lanes. |
| B2 | hard, L | It uses A2, BE word parsing, padding (`sha256Pad` byte-level vs `Reference.pad` bit-level), and `MerkleDamgard.iterate` vs `sha256Compress'`. It is easier against the `Fast` byte layer, or against a byte-list MD view provided by hash-specs. |
| D1 | M | `Nat`-word arithmetic modulo 2^64 vs `UInt64`; it needs the bound hypotheses (§7). Uses `blake2bF_eq`. |
| D2 | M | depends on the hash-specs RIPEMD-160 design |

Once B1 and B2 are proved, `@[csimp] theorem keccak256_csimp : @keccak256 = @keccak256Fast` (where `keccak256Fast m := (Hash.keccak256 (ofBVs m)).toBVs`) makes compiled code (the SpecRef interpreter, the `specref-eest-check` EEST runner and `#guard`) use the fast `ByteArray` implementation. It leaves the kernel definition, every proof and every `decide` KAT untouched, and adds no axioms.

## 6. Gaps in hash-specs

1. **A release at evm-asm's toolchain** (`v4.33.0`, or `v4.33.1` if evm-asm takes riscv-zkvm `v0.4.0`), pinned to Mathlib `db584cd`. This is the blocker.
2. **RIPEMD-160.** It is missing entirely. It is needed for precompile 0x03. evm-asm's `Ripemd160.hash` is a usable porting source: I checked it against Python `hashlib.new("ripemd160")` on 309 inputs (lengths 0–299, 407, 408, 543, 544, 1000, 1087–1089, 4096), with 0 mismatches.
3. **Byte-list (`List (BitVec 8)`) and lane-list (`List (BitVec 64)`) adapters**, plus list-level sponge and MD views (§4).
4. **`BitVec 64`/`BitVec 32`-typed wrappers or `@[simp]` width lemmas** for `Reference.G/round/F/compress` at `blake2bParams`/`sha256` (§7).
5. **An exposed Keccak-f over `List (BitVec 64)`** would let riscv-zkvm-style models bridge with `rfl` per round. This is optional, and A1 works without it.
6. **SLH-DSA instantiation** (FIPS 205 §11) for `SLHDSA.Primitives`. The SHAKE variant needs only `Hash.shake256` (available). The SHA-2 variant needs HMAC and MGF1, which are a v1 non-goal (ROADMAP §0). This is optional and far off.
7. **EVM precompile wrappers.** `Hash.blake2bPrecompile` already matches `pBlake2f`'s parsing (`Except String ByteArray`, f > 1 rejected). A RIPEMD-160 precompile helper (12 zero bytes ++ digest) is trivial on the evm-asm side and does not need to live in hash-specs.

## 7. Discrepancies

I ran a differential check with the evm-asm and riscv-zkvm definitions copied verbatim into `evidence/evm-asm/Check.lean`, run under hash-specs `98c225d` with `lake env lean --run`. Results:

| Comparison | Inputs | Result |
|---|---|---|
| `SpecRef.keccak256` vs `Hash.keccak256` | 309 lengths (0–299 and rate boundaries 407/408/543/544/1087–1089/4096) | 0 mismatches |
| `SpecRef.sha256` vs `Hash.sha256` | same | 0 mismatches |
| `Accel.keccakF` vs `Fast.keccakF` | 200 random 25-lane states, plus lengths 0/1/24/26/30 | 0 mismatches; both normalise to 25 lanes |
| `Accel.sha256Compress` vs `Reference.compress sha256` | 200 random (8, 16)-word pairs | 0 mismatches |
| `Accel.blake2bRound i` vs `Reference.round blake2bParams m v i` | 200 random, i = 0..199 (covers `idx % 10`) | 0 mismatches |
| `SpecRef.Blake2b.compress` vs `Hash.blake2bF` | 200 random, rounds ∈ {0,1,2,9,10,11,12,13,20,24,100}, f alternating, t1 ≠ 0 | 0 mismatches |
| `SpecRef.Ripemd160.hash` vs Python hashlib | 309 lengths | 0 mismatches |

No behavioural bug was found on either side. Some edge-case and spec-level notes:

- **`Accel.sha256Compress` with `hs.length < 8`** returns fewer than 8 words (`ZiskAccel.lean:284`, `zipWith` over `hs.take 8`), while `Reference.compress` returns 8. This is unreachable from `execCsrs`, which always reads 4 dwords (= 8 u32s), but bridge A2 needs the hypothesis `8 ≤ hs.length`.
- **SpecRef BLAKE2/RIPEMD on out-of-range `Nat` words.** `Blake2b.rotr` (`PrecompilesHash.lean:184-185`) computes `(x >>> n ||| x <<< (64-n)) % 2^64`, so any bits of `x` at or above 2^64 shift into the result. `v.set 12 (v[12] ^^^ t0)` (`:205`) does not reduce `t0`. The results therefore differ from the `UInt64` semantics if `h`, `m`, `t0` or `t1` are ≥ 2^64. This is unreachable from `pBlake2f`, whose words come from 8-byte LE slices. Bridge D1 needs bound hypotheses.
- **Order of gas and flag check in `pBlake2f`** (`:235-236`): it charges gas, then rejects `f ∉ {0,1}`. This matches execution-specs. `Hash.blake2bPrecompile` has no gas and rejects `f > 1` first. That is a scope difference, not a discrepancy.
- **hash-specs typing issue.** `Reference.G blake2bParams` is typed at `BitVec blake2bParams.w`, and `blake2bParams` is a `def` (`BLAKE2/Reference.lean:160`). A `simp only [..., blake2bParams]` while proving A3 failed with "Application type mismatch … `HAdd (BitVec Hash.BLAKE2.blake2bParams.w) …` but is expected to have type `HAdd (BitVec 64) …`". Downstream bridges will hit this; see gap 4. `SHA2.sha256.w` probably has the same issue (**unverified**).
- **Documentation nit (evm-asm).** `SLHDSA/DemoInstance.lean:6-7` says `mix h x = (h ^^^ x) * K` ("XOR + MUL"), but the definition at `:41` is `h + x` (docstring at `:35`: "A single RV64 `ADD`").
- **Coverage note (evm-asm).** The segmented Keccak top theorem `kssDigest_eq_specref` is stated only for `msg.length ≤ 135` (`HashBridgeKeccakSegTop.lean:78`). Open issues #12778 and #13014 record further envelope assumptions on the Keccak seam. None of this concerns hash-specs.

## 8. PR plan

**Repo conventions.**

- PR titles use conventional commits, `type[(scope)]: subject` (AGENTS.md:453), for example `proof: …`, `feat(bal): …`, `fix(ci): …`, `chore: bump to Lean v4.33.0 …`.
- Commits by AI need a `Co-Authored-By` line (AGENTS.md:452). There is no other AI-disclosure rule.
- Before review: `lake build` with no `sorry`, `scripts/check-forbidden-tactics.sh` (no `native_decide`/`bv_decide`), `scripts/check-axioms.sh` and `lake exe axiomsweep` (classical axioms only), `scripts/check-file-size.sh`. Do not add `set_option maxHeartbeats/maxRecDepth`, and import every new file into the default target (CONTRIBUTING.md).
- CODEOWNERS (`@pirapira`) covers `/lakefile.toml`, `/lean-toolchain`, `/EvmAsm/Rv64/`, `**/Spec.lean`, `/EvmAsm/EL/Conformance/`, `/EvmAsm/Progress/`, and the CI workflows. Putting bridge files outside `/EvmAsm/Rv64/` avoids the code-owner gate for everything except the lakefile change.
- CI checks the Rv64 shims against the dependency (`build.yml:314`). Its cache keys hash `lake-manifest.json`, so adding a dependency invalidates the package cache once.
- Open items touching these files: PR #13262 (K146 tx signing-hash triple; it consumes `keccakBodyDigest`, unaffected), and issues #12778, #13014, #12038, #13264. No open PR or issue mentions hash-specs.

**Prerequisites in hash-specs.**

| # | Title | Content | Size | Risk |
|---|---|---|---|---|
| HS-1 | `build: release the core package for Lean v4.33.0` | branch or tag `v4.33.0`: `lean-toolchain`, Mathlib `v4.33.0`, core `Hash` only; release workflow | S–M | core builds unchanged on 4.33.0 (verified); the zk package cannot follow unless CompPoly has a v4.33 tag (**unverified**) |
| HS-2 | `feat(prelude): List (BitVec 8)/(BitVec 64) adapters for ByteArray and lanes` | `ofBVs`/`toBVs`, lane adapters, round-trip lemmas | S | none |
| HS-3 | `feat(keccak,sha2): list-level sponge and Merkle–Damgård views` | `List`-based `keccak256`/`sha256` proved equal to `Hash.keccak256`/`Hash.sha256`, plus `BitVec 32/64`-typed wrappers and width `simp` lemmas | M | API naming |
| HS-4 | `feat(ripemd): RIPEMD-160 reference, fast, equivalence, KATs` | new family; RIPEMD-160 test vectors; fuzzing against hashlib/OpenSSL | L | new family; needs the README and assurance table per ROADMAP §9 |

Each of HS-2 to HS-4 must also land on the v4.33 release line (a patch tag) for evm-asm to use it.

**PRs in evm-asm**, in order:

| # | Title | Files | Lakefile | Deleted / kept | Proof rework | Size | Risks |
|---|---|---|---|---|---|---|---|
| E-1 | `chore(deps): require hash-specs v4.33.0` | `lakefile.toml`, `lake-manifest.json`, optionally one import smoke file | `[[require]] name = "hash-specs"`, `git = "https://github.com/Verified-zkEVM/hash-specs"`, `rev = "v4.33.0"`, placed after `mathlib` | nothing | none | XS | code-owner review; Mathlib rev must equal `db584cd` or the prebuilt oleans are rejected; cache churn |
| E-2 | `proof(hash-specs): ZisK permutations agree with hash-specs` | new `EvmAsm/HashSpecs/Accel.lean` (non-module or `module`) | none | keep everything | none (new theorems A1–A3) | M (≈400–700 lines) | the typing issue (gap 4; better after HS-3) |
| E-3 | `proof(hash-specs): SpecRef keccak256/sha256 equal Hash.keccak256/Hash.sha256` | new `EvmAsm/HashSpecs/Crypto.lean` | none | keep | none (new theorems B1–B2) | L (M after HS-3) | proof effort; elaboration memory (#12755) |
| E-4 | `proof(hash-specs): SpecRef BLAKE2F equals Hash.blake2bF` | new `EvmAsm/HashSpecs/Blake2f.lean`; optionally a `pBlake2f` output lemma against `Hash.blake2bPrecompile` | none | keep | none | M | `Nat` bounds |
| E-5 | `perf(specref): evaluate keccak256/sha256 via hash-specs (csimp)` | `Stateless/SpecRef/Crypto.lean` or a new file after E-3 | none | keep definitions | none | S | changes compiled behaviour of the EEST runner; measure first |
| E-6 | `refactor(specref): take RIPEMD-160 and BLAKE2F from hash-specs` (after HS-4 and E-4) | `PrecompilesHash.lean` (`pRipemd160`, `pBlake2f` call `Hash.*`; delete `Ripemd160` and `Blake2b` namespaces, about 190 lines; keep gas and `#guard`s) | none | delete the SpecRef primitive ports | none (no proof uses them) | S | maintainer judgement: SpecRef is meant to mirror execution-specs line by line |
| E-7 (optional) | `feat(slhdsa): SHAKE256 instance of SLHDSA.Primitives` | new `SLHDSA/Concrete/Shake.lean` using `Hash.shake256` | none | keep `DemoInstance` | none | M | out of scope for the RV64 demo verifier |

Do **not** replace `Accel.*` or `SpecRef.keccak256`/`sha256` definitionally. They are the kernel-reducible targets of about 28.8k lines of proofs and of `decide` KATs.

## 9. Open questions for the maintainers

1. Given README's "direction under reconsideration" note and #13264 (Pancake), is a hash-specs dependency wanted at all, or only for the SpecRef port and EEST runner (E-5, E-6)?
2. Which Lean version should we release at: v4.33.0 (current), or v4.33.1 together with riscv-zkvm `v0.4.0`? Is a move to v4.35 planned once riscv-zkvm PR #19 resumes?
3. Should bridge files sit outside `/EvmAsm/Rv64/` (no code-owner gate), or with the accelerator model?
4. Is it acceptable to delete SpecRef's own RIPEMD-160 and BLAKE2b ports (E-6)? Or should SpecRef stay self-contained, mirroring execution-specs, with bridges only?
5. Would you accept `@[csimp]` to speed up the SpecRef interpreter? Or must compiled evaluation stay on the list definitions for byte-identity reasons?
6. For SLH-DSA, is a concrete FIPS 205 instance (SHAKE) planned, or is the demo instance the end state?

---

## 10. `riscv-zkvm`: its single hash file

- **Snapshot.**
  - HEAD `6810fc1` (2026-10-06), `lean4:v4.33.1`, tags `v0.1.0`–`v0.4.0`. evm-asm uses `v0.3.0` (`v4.33.0`).
  - The only requirement is Sail (`079463…` at HEAD; `dhsorens/lean-sail@8d57a8b` at v0.3.0). There is no Mathlib.
  - `lakefile.toml`, module system, `fixedToolchain = true`, prebuilt oleans.
  - PR #19 (Lean 4.35, lean-sail v7) is a paused draft.
- **File.** `RiscvZkvm/Rv64/ZiskAccel.lean` (907 lines) holds every inventory row of §2A: `keccakF`, `sha256Compress` and `blake2bRound` with `decide` KATs, plus `csrsWrite`/`execCsrs`/`csrsValid` for CSR ids 0x800, 0x805 and 0x819 (also the non-hash 0x802–0x810 arithmetic and curve accelerators). It is imported by `Rv64/Instructions.lean:10`, where `.CSRS csr rs1 => s.execCsrs csr rs1` is at `:281`, and by `Interpreter/State.lean:90`.
- **Duplication with evm-asm: none.** `EvmAsm/Rv64/ZiskAccel.lean` is a generated `export` shim (same constants). The upstream file is identical at `v0.3.0` and HEAD.
- **Nature.** Executable concrete semantics of hardware accelerators, deliberately not axiomatised. The Keccak, SHA-256 and BLAKE2b functions are exactly what the ZisK precompiles are *assumed* to compute. A bridge to hash-specs (A1–A3) therefore certifies the assumption's *target*: if the ZisK circuit implements Keccak-f, SHA-256-compress or BLAKE2b-round as standardised, the model is right. It says nothing about whether ZisK actually does. All three agree numerically with hash-specs (§7).
- **Recommendation: no hash-specs dependency in riscv-zkvm.**
  - It would add Mathlib to a deliberately Mathlib-free model (Lake fetches every `require`, whatever the library).
  - It would tie riscv-zkvm's toolchain to ours.
  - Put bridges A1–A3 in evm-asm (which already has Mathlib) or in a separate bridge package.
  - In riscv-zkvm, at most a docstring cross-reference to `Hash.Keccak.Fast.keccakF`, `Hash.SHA2.Reference.compress` and `Hash.BLAKE2.Reference.round`, with a link to the bridge. PR title per repo convention: `docs(zisk): cite hash-specs for the accelerator permutations`. Size XS.
- **Gap for riscv-zkvm itself:** none. A `List (BitVec 64)` Keccak-f in hash-specs (gap 5) would only shorten A1.
