# Upstreaming plan: hash-specs across Verified-zkEVM

Researched 2026-10-27 against each repo's `HEAD` and hash-specs `98c225d` (`v4.35.0-patch1`).

- **Records.** One per repo (ROADMAP §6.1); each gives a snapshot, an overlap inventory, call
  sites, adapter lemmas, bridge statements, gaps, discrepancies, a PR plan and open questions.
- **Evidence.** The checks and proofs behind them are in [`evidence/`](evidence/).
- **Status.** Nothing has been sent to any repo yet. No PRs, issues or comments.

| Record | Repo | Toolchain | Overlap with hash-specs | Readiness |
|---|---|---|---|---|
| [`vcvio.md`](vcvio.md) | VCVio `575962c` | v4.35.0 | SHA-2, SHA-3, SHAKE, Keccak-256 (+ HMAC, MGF1) | **Ready.** Same pins; three small hash-specs additions first. |
| [`arklib.md`](arklib.md) | ArkLib `59e5b77` | v4.35.0 | Poseidon2 KoalaBear t=16/24; duplex sponge (abstract) | **Ready** for a bridge; the instance choice is the maintainers'. |
| [`clean.md`](clean.md) | clean `0d76409` | v4.33.1, draft #487 → v4.35.0 | Keccak-256, SHA-256, BLAKE3, circomlib Poseidon | After #487; **two bugs in clean** to report first. |
| [`leanervm.md`](leanervm.md) | leanerVM `a37b2b0` | v4.34.1 | BLAKE2s | Needs a hash-specs `v4.34.1` release and two-flag BLAKE2 compression. |
| [`evm-asm.md`](evm-asm.md) | evm-asm `7e65e4d` (+ riscv-zkvm `6810fc1`) | v4.33.0 | Keccak-f, SHA-256 compression, BLAKE2b (ZisK accelerators); keccak256/sha256; RIPEMD-160, BLAKE2F precompiles | Needs a v4.33 release line; project direction under reconsideration. |
| [`machine-checked.md`](machine-checked.md) | machine-checked `5b1f8a5` | v4.33.0 | BLAKE2b (Zip2005); BLAKE2s (LeanVM case, no spec yet) | Policy is to **port, not depend**: copy our reference with provenance. |
| [`zklean.md`](zklean.md) | zkLean `eb17e50` (upstream GaloisInc `014fa39`) | v4.25.2 | Keccak-f / SHA3-256 (an example) | Low value; Keccak-f bridge already proved; blocked on a 10-release toolchain bump. |
| [`other-repos.md`](other-repos.md) | leanth, verified-zkevm.org, hax, rust-lean, Overview, PolyFun, loom2, iris-lean, CompPoly | various | leanth: leanVM Poseidon1 KoalaBear (PR #18) | leanth is worth an early conversation; the site entry is a one-line PR. |

## What we found

**Agreement.** Every overlapping spec was run against ours on verbatim copies of its definitions,
and the bridge proofs below were checked. No case shows hash-specs computing the wrong thing.

| Repo | Checks against hash-specs | Result |
|---|---|---|
| VCVio | 5,878 differential checks (SHA-2, SHA-3, SHAKE, Keccak-256) plus all of VCVio's KATs | 0 mismatches |
| evm-asm | `keccak256` and `sha256` at 309 lengths; ZisK permutations at 200 random inputs each | 0 mismatches |
| evm-asm | its RIPEMD-160 against Python's `hashlib` | agrees |
| leanerVM | BLAKE2s at every length 0–300 | 0 mismatches |
| machine-checked | BLAKE2b with personalisation, at several output lengths | 0 mismatches |
| zkLean | Keccak-f **proved** equal to ours (`evidence/zklean/Bridge.lean`); SHA3-256 on 1,800 messages | 0 mismatches |
| clean | Keccak-f **proved** equal through #489's view (`evidence/clean/KeccakBridge.lean`); SHA-256, BLAKE3 compression, Poseidon t=2..5 | agree where clean's specs are correct |
| ArkLib | its Poseidon2 permutation | agrees, given the same constant order (see below) |

**Bugs and discrepancies in other repos.** None reported yet; report them only with your approval.

1. **clean, Keccak absorb (serious).**
   - The bug: `Specs.Keccak256.absorbBlock` (`Clean/Specs/Keccak256.lean:156`) and the `AbsorbBlock` circuit XOR `block[i]` into `state[i]`.
   - Why it is wrong: clean indexes lanes as `5x+y` (`thetaC`, l.26–32), so this writes message words into capacity lanes 17, 20, 21 and 22.
   - Consequence: no block encoding makes `absorbBlocks` equal Keccak-256, so `KeccakInductive.tableStatement` claims more than it proves.
   - Evidence: on the empty message, clean gives `0eab42de…`; transposed, it gives the correct `c5d24601…`. clean's own Python oracle transposes correctly.
2. **clean, BLAKE3 `processChunk`.** It applies keyed-hash and derive-key flags only to a chunk's last block (`BLAKE3.lean:267`). Plain hashing is unaffected.
3. **ArkLib, Poseidon2 instance.**
   - The old indexing bug noted in ROADMAP §3 was **fixed upstream in ArkLib #1316**.
   - ArkLib now implements the *pre-0.6* Plonky3/leanSpec constant order, while we implement Plonky3 0.8.0.
   - Both are internally consistent. ArkLib's test names `default_koalabear_poseidon2_16` without a version, which is now ambiguous.
   - A draft issue is in `arklib.md` §8.
4. Minor items, listed in the records:
   - evm-asm: a docstring nit.
   - VCVio: an unreachable padding branch, already tracked in #629.
   - zkLean: a fragile but correct absorb bound.
   - machine-checked: links to the old `dhsorens/hash-specs` URL.
   - loom2: its `lean-toolchain` is `master`.

**Bugs and gaps in hash-specs.**

- **Performance bug, confirmed.**
  - `Hash.Keccak.Fast.squeeze` (`Hash/Keccak/Fast.lean:104–107`; the same in `Stream.lean`) evaluates one Keccak-f too many.
  - The last step's `keccakF a` argument is computed eagerly and then discarded, so short SHA-3, SHAKE and Keccak-256 calls do two permutations instead of one.
  - In the interpreter this measured 2.58× slower than VCVio's SHAKE.
  - It matters because VCVio runs SLH-DSA-SHAKE KATs on every PR.
- **Typing friction.** `Reference.G blake2bParams` lives in `BitVec blake2bParams.w`, not `BitVec 64`. A downstream bridge hit an ill-typed `HAdd` when unfolding. We need `BitVec 64`/`BitVec 32`-typed wrappers or width `simp` lemmas; SHA-2 likely has the same issue.
- **Stale documentation.**
  - The kernel claim: `Hash/ZK/Poseidon2/README.md:178` and `Hash/ZK/Common/Grain.lean:30` say Grain constants cannot be checked in the kernel. That holds for BN254, but the 31-bit fields check in about 4 s each with `decide +kernel`.
  - ROADMAP §1 is out of date:
    - VCVio's hashes moved to `VCVio/Algorithms/`.
    - ArkLib is on v4.35.0.
    - The ArkLib bug noted in §3 has since been fixed.
    - It lacks machine-checked, riscv-zkvm and leanth.
  - The known `InstanceParams.lean` docstring problem: it mentions nonexistent width-32 instances and omits the ±3 diagonals.

## Work in hash-specs first

These are our own changes, which we can make without asking anyone. They are grouped into
releases, and the records cite them by their local IDs (shown in brackets).

| # | Change | Needed by | Size |
|---|---|---|---|
| P1 | `perf(keccak)`: drop the trailing permutation in `Fast.squeeze` and `Stream.squeezeBytes`, and re-prove `Equiv`/`StreamLemmas` | VCVio (H2) | S–M |
| P2 | Output-size `@[simp]` lemmas for the byte API (`shake256_size`, `sha3x256_size`, `sha256_size`, …), plus `size_keccakF` and `F_length` | VCVio (H1), clean (H1), machine-checked (H1) | S |
| P3 | Keccak: named `Fast.absorb`, with `sponge_eq_absorb` and `keccak256_eq_absorb`; a lane-function view | clean (H1), ArkLib (H4, later) | S |
| P4 | Adapters: `List (BitVec 8)` ↔ `ByteArray`, `List (BitVec 64)` lanes, list-level sponge and Merkle–Damgård views; `BitVec 64/32`-typed wrappers for the BLAKE2 and SHA-2 reference functions | evm-asm (HS-2, HS-3), all bridges | M |
| P5 | BLAKE2: compression taking both flag words (last block and last node), with today's `F` as a special case; a `Hash.blake2sF` entry point; lemmas for one- and two-block messages | leanerVM (H2), machine-checked (H1, H2) | M |
| P6 | HMAC (FIPS 198-1) and MGF1 (RFC 8017), generic over the hash; RFC 4231 KATs | VCVio (H3) | M |
| P7 | Poseidon2: `Reference.permutation_congr`; kernel theorems tying the KoalaBear and BabyBear Grain samples to literal tables; doc fixes. The pre-0.6 instance is needed **only if** ArkLib keeps it. | ArkLib (H0–H3) | S |
| P8 | Docs: refresh ROADMAP §1; fix the `InstanceParams` docstring and the README kernel claims | — | XS |
| P9 | RIPEMD-160 family: reference, fast, `Equiv`, KATs, fuzzing | evm-asm (HS-4) | L |
| P10 | circomlib's *optimized* Poseidon (folded constants, sparse matrices), with an equivalence theorem against the reference | clean (H2) | L |
| P11 | leanVM's Poseidon1 KoalaBear t=16 instance (x³ S-box, 4+20+4 rounds) | leanth | S–M |

**Release lines.** Downstream projects pin our tags, and `fixedToolchain` means the toolchains
must match exactly.

- **`v4.35.0-patch2`**, after P1–P3, P6 and P8. This covers VCVio, ArkLib and clean once clean is on v4.35.
- **`v4.34.1`**, for leanerVM: a branch from tag `v4.34.0`, with the toolchain and Mathlib moved to v4.34.1, and P5 backported as `v4.34.1-patch1`. ROADMAP §2.1 records that v4.34.1 builds.
- **`v4.33.0`**, for evm-asm. It would also serve machine-checked, but only if that repo makes an exception to its port-not-depend rule.
  - **Verified 2026-10-27:** the core package (`Hash`, `HashTests`) at `98c225d` builds unchanged on Lean v4.33.0 with Mathlib v4.33.0, with 0 errors and 0 warnings. Only `lean-toolchain` and the Mathlib `rev` changed.
  - Only the core is needed here: neither evm-asm nor machine-checked uses CompPoly or the zk package.
  - Mathlib `v4.33.0` resolves to `db584cd`, the same commit that evm-asm and machine-checked pin.
- **Process.** Each extra line is a maintenance cost. Keep these as release branches, and backport only what a consumer needs.

## PRs to other repos, in order

The waves are ordered by readiness and value; within a repo, follow its record's order.

**Wave 0: reports and coordination (no code).** Each needs your go-ahead.

- clean:
  - Issue or fix PR for the Keccak absorb lanes. This is independent of us and worth doing now.
  - Issue for the BLAKE3 flags.
- ArkLib: the instance-pinning issue (`arklib.md` §8).
- leanth: talk to the author of PR #18 before it merges, so its Poseidon can be stated against `Hash.ZK.Poseidon.Reference`.
- verified-zkevm.org: list hash-specs among the repositories (`Data.lean`, around l.987).
- machine-checked: update the hash-specs URL to the new repo (their M1).

**Wave 1: same toolchain, after `v4.35.0-patch2`.**

- VCVio:
  - V1: require hash-specs. It goes before the Mathlib line, as `«hash-specs»`, and the import checker's whitelist must allow it.
  - V2: a one-shot cutover that deletes about 280 lines; VCVio's rules forbid shims.
  - V3: switch to our HMAC and MGF1.
  - V4a: a nightly agreement test of the FFI SHA-3 against our spec.
  - **Coordinate with draft #910**, which proves facts about `VCVio.Algorithms.Sha2`.
- ArkLib:
  - A1: require hash-specs, and prove `Poseidon2.permute` equal to our reference permutation, given ArkLib's tables (M, 200–400 lines).
  - A2 (optional): define the parameters from hash-specs.
  - A4 (later): Keccak for `generateTag`, after open PRs #469 and #848.

**Wave 2: after a dependency moves.**

- clean, after #487 moves it to v4.35:
  1. Fix PRs first.
  2. Require hash-specs.
  3. Keccak bridges (Appendix A of `clean.md` is ready).
  4. SHA-256 bridge.
  5. BLAKE3 bridge.
  6. Later, the Poseidon bridge, after #465 and P10.
- leanerVM, after the `v4.34.1` release:
  - L1: compression bridge, together with the require; their policy needs a named consumer.
  - L2: byte-level bridge.
  - L3: the opcode relation through our two-flag compression (P5).
  - New files only, to avoid conflicts with the 43-PR stack on issue #12.

**Wave 3: blocked or optional.**

- evm-asm:
  - It needs the v4.33 line, or a toolchain bump that waits on riscv-zkvm PR #19, which is paused.
  - The PRs would be bridge theorems only (E-2 to E-4). Their list-based specs stay, because about 28.8k lines of proofs and the `decide` KATs depend on them.
  - The project's direction is under reconsideration (issue #13264), so keep the investment small.
- machine-checked: port our `Hash/BLAKE2/Reference.lean` and `Prelude/Bits.lean`, which need only core Lean, with provenance; then bridge the Zip2005 BLAKE2b model.
- zkLean:
  - These go to **GaloisInc/zkLean**, not the Verified-zkEVM copy.
  - First a toolchain bump; then an examples-only dependency and the proved Keccak-f bridge.
- hax and rust-lean: optional later examples; see `other-repos.md`.

## Conventions to respect

Every record lists its repo's rules. The ones that change how PRs are written:

- **AI attribution.**
  - VCVio and leanerVM forbid AI-attribution lines.
  - evm-asm requires a `Co-Authored-By` trailer on AI commits. Decide how to handle that before contributing there, since our own commits carry no co-author trailers.
  - zkLean and clean have no rule; past clean PRs stated AI use.
- **Proof checking.**
  - ArkLib and machine-checked forbid `native_decide`.
  - evm-asm also forbids `bv_decide`.
  - Our `Equiv` theorems use only `propext`, `Classical.choice` and `Quot.sound`, so their axiom audits pass.
- **Shims.** VCVio forbids deprecated aliases; machine-checked requires them when a statement changes.
- **Discussion first.** ArkLib and leanerVM want an issue or design discussion before large PRs.
