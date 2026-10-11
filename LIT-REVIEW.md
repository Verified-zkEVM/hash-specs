# Literature Review: Formal Specifications of Hash Functions

*Compiled 2026-10-11 with a deep-research workflow: 5 search angles, 21 sources fetched, 94 claims extracted, 25 claims adversarially verified by 3-agent voting (24 confirmed, 1 refuted). Extended the same day by a gap-closing pass (§5) covering Cryptol/SAW, ACL2, Isabelle, Coq/Rocq beyond VST, HOL4/CakeML, more Lean work, and ZK-circuit verification groups.*

**How to read this:**
- Sections 1–3 hold claims that survived 3-vote adversarial verification (a claim is dropped if 2 of 3 voters refute it).
- Section 4 lists leads from the first run that the verification pass didn't reach. All of them have since been checked against their repos (marked ✔ below).
- Section 5 is the gap-closing pass. Every item was checked against a primary source, by reading the repo tree or files with `gh api`, the AFP mirror, or the paper. The most significant items were spot-checked a second time. They did **not** go through 3-vote adversarial verification, and "proved" here means the files exist and state the theorem; the proofs were not rebuilt.
- Section 6 lists what is still missing, §7 ranks the sources, and §8 draws conclusions for this project.

---

## TL;DR

| Hash | Best formal spec today | Prover | Maturity |
|---|---|---|---|
| SHA-256 | Appel, VST/FIPS 180-4 spec (TOPLAS 2015) | Coq | Peer-reviewed, gold standard |
| HMAC-SHA-256 | Beringer et al. (USENIX Sec 2015) | Coq (VST + FCF) | Peer-reviewed |
| SHA-2 family | HACL* specs | F* | Peer-reviewed, industrial |
| SHA-3 / SHAKE | Almeida et al. (CCS 2019) | EasyCrypt/Jasmin | Peer-reviewed, includes security proof |
| SHA-3 / SHAKE | HACL*, libcrux (hacspec/F*/EasyCrypt) | F*, EasyCrypt | Industrial |
| SHA-3 / SHAKE, SHA-2 | Microsoft SymCrypt/Aeneas (arXiv 2609.15648) | **Lean 4** | Preprint (Sept 2026); best Lean candidate |
| Keccak-256 (Ethereum) | HOL4 `keccak` theory (Trindemossen 1) | HOL4 | Shipped in HOL4 release |
| Keccak-f / SHA-256 / SHA-512 | Axiom openvm-fv reference specs (FIPS 202, 180-4) | **Lean 4** | Used for circuit soundness; axiom-audited, no `native_decide` (§4) |
| Keccak-256 | HOL4 `Keccak_256_w64_thm` (optimized = spec) | HOL4 | Released library, cheat-free since 2026-09 (§5.5) |
| SHA-2 family (all 7) | AFP `Crypto_Standards` (FIPS 180-4, plus HMAC FIPS 198-1) | Isabelle | AFP entry, reads like the standard (§5.3) |
| SHA-2, SHA-3 | Galois `cryptol-specs` ("gold standard" specs); AWS-LC SAW proofs | Cryptol/SAW | Industrial; backs AWS-LC SHA-384/512 proofs (§5.1) |
| SHA-2, Keccak/SHA-3, BLAKE2 | Kestrel crypto books | ACL2 | Maintained library with test suites (§5.2) |
| SHA-512 (Arm asm) | LNSym (AWS) | **Lean 4** | Arm assembly proved against a Lean spec (§5.6) |
| BLAKE2 | HACL*, libcrux; also Cryptol, ACL2 | F*, hacspec, Cryptol, ACL2 | Industrial |
| BLAKE3 | `clean` Specs/BLAKE3 (Verified-zkEVM) | **Lean 4** | Spec plus circuit gadgets; no standalone reference library |
| RIPEMD-160 | Isabelle/SPARK (implementation proof); HOL4 spec | Isabelle, HOL4 | Mature (§5.3, §5.5) |
| Poseidon | Clean (circomlib BN254, arity 1: sound + complete); Kestrel (Aleo BLS12-377 R1CS); Garden (Halo2/Orchard, Pallas t=3); Reilabs (gnark BN254) | **Lean 4**, ACL2, Rocq | Several narrow, instance-specific results (§5.7) |
| Poseidon2 | ArkLib spec (KoalaBear); Lampe (Noir sponge, permutation trusted) | **Lean 4** | Specs only; no verified permutation circuit confirmed |
| MiMC | Kestrel MiMCSponge spec + Semaphore R1CS soundness | ACL2 | Mature but old (2020–21) (§5.2) |
| Pedersen hash | Kestrel Zcash Sapling spec with injectivity proofs; Lampe (Noir, Grumpkin) | ACL2, **Lean 4** | Spec-level (§5.2, §5.7) |
| Rescue, Rescue-Prime, RPO, Anemoi, Griffin, Monolith, Tip5 | **None found** | — | Gap |

**Bottom line for a Lean 4 hash-spec effort:**
- For SHA-2 and SHA-3, the existing references are Coq, EasyCrypt and F*. The newest and most complete Lean 4 specs are the SymCrypt/Aeneas FIPS 202 and FIPS 180-4 specs, the Nethermind LeanCrypto Keccak-256, and the Axiom openvm-fv Keccak and SHA-256 specs.
- Outside Lean, the byte-oriented hashes are well covered: Cryptol, ACL2, Isabelle and HOL4 all have executable SHA-2 specs, and most have SHA-3 too.
- ZK-friendly hashes are covered only by **narrow, instance-specific** results (one Poseidon instance per project), with no reusable library. No artifact proves circomlib's optimized Poseidon equal to the textbook algorithm for all inputs. Rescue-family and newer designs have nothing at all. That is the main open space.

---

## 1. Mature, peer-reviewed specifications (non-Lean)

### 1.1 Coq / VST: SHA-256 and HMAC (high confidence)

- **Appel, "Verification of a Cryptographic Primitive: SHA-256"**, ACM TOPLAS 37(2), 2015. [PDF](https://www.cs.princeton.edu/~appel/papers/verif-sha-2.pdf)
  - Proves OpenSSL's SHA-256 C code functionally correct against a Coq formalisation of FIPS 180-4, carried down to x86 assembly via CompCert.
  - The SHA-256-specific spec is about 169 lines of Coq and can be executed. It was cross-checked against reference implementations, by testing rather than proof.
  - *Caveats:*
    - OpenSSL was lightly modified (macros expanded).
    - Covers SHA-256 only.
    - The CompCert x86 model, the assembler and the hardware are trusted.
- **Beringer, Petcher, Ye, Appel, "Verified Correctness and Security of OpenSSL HMAC"**, USENIX Security 2015. [link](https://www.usenix.org/conference/usenixsecurity15/technical-sessions/presentation/beringer)
  - VST proves the C code implements its FIPS functional spec. FCF proves that spec is a PRF.
  - *Caveat:* the PRF result assumes the SHA-256 compression function is a PRF.

### 1.2 EasyCrypt / Jasmin: SHA-3 (high confidence)

- **Almeida, Baritel-Ruet, Barbosa, Barthe, Dupressoir, Grégoire, Laporte, Oliveira, Stoughton, Strub, "Machine-Checked Proofs for Cryptographic Standards: Indifferentiability of Sponge and Secure High-Assurance Implementations of SHA-3"**, ACM CCS 2019. [ePrint 2019/1155](https://eprint.iacr.org/2019/1155) · [NSF PAR](https://par.nsf.gov/biblio/10161927)
  - Machine-checked proof that the SHA-3 sponge is indifferentiable from a random oracle. The authors note this implies collision, preimage and second-preimage resistance.
  - A vectorised (AVX2) Jasmin implementation is proved correct against the EasyCrypt SHA-3 spec and constant-time in an idealised leakage model.
  - *Caveats:*
    - Indifferentiability assumes Keccak-f[1600] is an ideal permutation, so it is a result about the mode, not the concrete permutation.
    - Reaching assembly relies on the separate Coq proof of the Jasmin compiler.

### 1.3 F* / HACL*: SHA-2, SHA-3, BLAKE2 (high confidence)

- **HACL\*** ([project-everest/hacl-star](https://github.com/project-everest/hacl-star), now [hacl-star/hacl-star](https://github.com/hacl-star/hacl-star); production builds are in hacl-packages).
  - Verified C produced from F*/Low* via KaRaMeL, plus Vale assembly.
  - Verified for memory safety, functional correctness and secret independence.
  - Includes SHA-2, SHA-3 and BLAKE2.
  - Its pure F* specs are among the most reliable machine-readable hash references.
  - *Caveat:* KaRaMeL is in the trusted base.

### 1.4 libcrux (Cryspen) and libjade (Formosa) (medium confidence)

- **libcrux** ([FMCP 2024 slides](https://cryspen.com/post/fmcp/Formal-Specifications-for-Certifiable-Cryptography-FMCP-2024.pdf))
  - Lists BLAKE2, SHA-2 and SHA-3, each with **hacspec** and F* specs. SHA-3 also has an EasyCrypt spec.
  - Implementations come from HACL* (BLAKE2, SHA-2) and from HACL* plus libjade (SHA-3).
  - *Caveat:* a self-reported vendor snapshot from 2024. SHA-3 has since moved to hax-based verification.
  - Relevant to Lean: hax has a Lean backend, which could be a route from hacspec specs to Lean.
- **libjade** ([formosa-crypto/libjade](https://github.com/formosa-crypto/libjade))
  - Jasmin implementations of SHA-256, SHA-512, SHA3-224/256/384/512 and SHAKE-128/256 (no BLAKE2), with interactive EasyCrypt correctness proofs.
  - *Caveats:*
    - The README calls verification "ongoing" for many implementations and has no per-primitive status table.
    - As of 2026-10-01 the hash sources live under `oldsrc-should-delete/`, so pin a commit if you cite them.

### 1.5 HOL4: Keccak / SHA-3 (high confidence)

- **HOL4 Trindemossen 1** (released 2024-04-25) ships a `keccak` theory. [release notes](https://github.com/HOL-Theorem-Prover/HOL/releases)
  - Defines the SHA-3 family via the Keccak permutation and sponge.
  - Includes Ethereum's **Keccak256**, which the release notes describe as the motivation.
  - Has a rudimentary computable version based on sptrees. Faster `cv_compute` evaluation is listed as future work.

---

## 2. Lean 4 specifications of SHA-2 and SHA-3

### 2.1 Microsoft SymCrypt via Aeneas: strongest Lean result (medium confidence: preprint)

- **Ho, Fournet, Protzenko, Naehrig, Clune, Longa, Boisseau, Leal Sánchez, Fromherz, Delignat-Lavaud**, [arXiv:2609.15648](https://arxiv.org/pdf/2609.15648) (v1, 14 Sep 2026).
  - Verifies SymCrypt's Rust SHA-3/SHAKE for functional correctness against a **Lean 4 FIPS 202 spec**, using Charon/Aeneas extraction and the Lean kernel. Also covers an experimental SHA-2 against a **Lean FIPS 180-4 spec**.
- *From extraction, not separately vote-verified:*
  - Size: the FIPS 202 spec is about 140 core lines plus 2,276 lines of proved spec properties (for example, that Keccak is a permutation and that the constant tables are correct). The FIPS 180-4 spec is about 205 core lines plus 2,020 lines of properties.
  - Bug found: verifying the incremental SHAKE API against the one-shot spec found a real bug in `extract`. It produces wrong bytes in multi-call SHAKE calls that start mid-lane.
- *Caveats:*
  - Not yet peer-reviewed.
  - The TCB includes Aeneas, `native_decide`, `bv_decide`, and hand-written axioms for SHA-NI and other intrinsics.
  - No constant-time guarantees.
  - **Open question:** whether the Lean specs are released as a standalone, reusable library.

### 2.2 Galois zkLean: Keccak spec and circuit soundness (medium confidence)

- [Galois article](https://www.galois.com/articles/zklean-a-dsl-for-zk-statement-verification) (J. Parker, 2026-03-16).
  - A Lean bitvector Keccak spec over 64-bit lanes (`keccakFSpec`, 24 rounds of `keccakRoundSpec` built from `thetaSpec`, `rho_piSpec` and others).
  - A field-arithmetic SHA-3 circuit is proved **sound** against it, round by round, using `Std.Do` Hoare triples.
  - *Caveats:*
    - Only soundness is shown, not completeness.
    - **Correction:** the first run refuted, 0–3, the claim that this circuit lives in the `GaloisInc/zkLean` repo. A direct check shows it does: spec, circuit and proofs are in `examples/zkLeanExamples/Sha3/` (`Spec.lean`, `Circuit/`, `Proof/`) of both `GaloisInc/zkLean` and `Verified-zkEVM/zkLean`, with no `sorry` in `Proof.lean`. The verifiers likely looked only at the library sources.

### 2.3 Doussot (NCC Group): SHA-3 in Lean 4 (medium confidence)

- **"Cryptography Experiments In Lean 4: SHA-3 Implementation"**, [ePrint 2024/1880](https://eprint.iacr.org/2024/1880).
  - Full SHA-3 family in Lean 4, with one-shot and streaming APIs and XOFs.
  - Some properties are formally proved.
  - Does not claim end-to-end verification against FIPS 202.
  - Not peer-reviewed. The specific proved properties were not confirmed because the PDF could not be fetched.

### 2.4 Not a spec: joehendrix/lean-crypto (high confidence)

- [joehendrix/lean-crypto](https://github.com/joehendrix/lean-crypto) has no hash spec in Lean.
  - SHAKE is an opaque `@[extern]` FFI call into vendored XKCP C code.
  - Reference specs are listed only as future work. Last commit 2024-09.

---

## 3. ZK-friendly hashes (verified claims)

Coverage is thin and immature (medium confidence):

- **reilabs/gnark-lean-demo** ([repo](https://github.com/reilabs/gnark-lean-demo))
  - A 42-line Lean Poseidon permutation spec (x^5 S-box, BN254, t=3), "very closely based on the Poseidon reference implementation".
  - A test vector is proved by `eq_refl`.
  - Used to show a gnark circuit equivalent to the spec. A demo, not a reference library.
- **AMO-Lean** ([Reservoir](https://reservoir.lean-lang.org/@manuelpuebla/amo-lean))
  - Poseidon2 (BN254, t=3) that passes HorizenLabs-compatible test vectors.
  - All 12 remaining `sorry`s are in Poseidon2.
  - Single-author project. Reservoir reports build failures on recent toolchains (v4.26–v4.32).

---

## 4. Additional leads (from primary sources; not adversarially verified)

These were extracted from fetched primary sources but were not put through the 3-vote verification pass. Each was later checked against its repository (✔). Several are probably the most directly useful items for a Lean 4 ZK hash-spec project.

- ✔ **Nethermind: Keccak-256 in Lean (LeanCrypto) and Scroll Halo2 circuit.** [blog](https://www.nethermind.io/blog/formal-verification-of-halo2-circuits-in-lean) · [NethermindEth/LeanCrypto](https://github.com/NethermindEth/LeanCrypto)
  - A hand-written mathematical Keccak-256 spec in Lean 4. *Repo check:* a single file, `LeanCrypto/Primitives/HashFunctions/Keccak256.lean` (~8 KB), with definitions (`keccak_round`, `keccakF`, `keccak256`) and no theorems. Toolchain `v4.18.0-rc1`, Apache-2.0, last push 2026-03.
  - The Halva tool extracts Halo2 constraints into Lean.
  - Proved that most Scroll Keccak circuit constraints imply the spec's absorb and squeeze phases (not full correctness).
  - Found an **underconstraint bug**: `is_final` could be set on an intermediate row to produce arbitrary output. A PoC is at `NethermindEth/scroll-keccak256-PoC`.
- ✔ **Axiom: OpenVM Keccak-f[1600] and SHA-256 circuits in Lean.** [blog](https://axiom.xyz/blog/fv-keccak-sha2) · [openvm-org/openvm-fv](https://github.com/openvm-org/openvm-fv)
  - Lean reference specs hand-written from FIPS 202 and FIPS 180-4 and audited by hand against the standards.
  - Proves that constraint satisfaction implies the reference hash. This is soundness; completeness is not discussed.
  - Proofs were generated by an agentic AI formalizer.
  - The TCB includes the circuit-to-Lean extraction and the specs.
  - *Repo check:* reference models in `VmExtensions/Keccak/Spec/` and `VmExtensions/Sha2`. SHA-512 compression is covered too, not just SHA-256. CI gates forbid `sorry`, `native_decide` and `bv_decide`, and an in-build `#audit_axioms` command allows only `propext`, `Classical.choice` and `Quot.sound`. Lean `v4.26.0`, Apache-2.0/MIT, last push 2026-07. This is a useful precedent for our axiom policy.
- ✔ **zkSecurity: Poseidon in Clean.** [blog](https://blog.zksecurity.xyz/posts/poseidon-clean/) · [Verified-zkEVM/clean](https://github.com/Verified-zkEVM/clean)
  - Soundness **and completeness** of a hand-modelled circomlib optimized Poseidon, for arity 1 (t=2) over BN254, against `Clean/Specs/PoseidonOptimized.lean`.
  - The repo also has a textbook spec, `Clean/Specs/Poseidon.lean`.
  - *Caveats:*
    - The two Poseidon specs are not proved equal; they are only cross-tested, including against circomlibjs vectors.
    - The Circom source is not parsed mechanically.
    - The blog said one `sorry` remained, for the primality of the BN254 prime. *Repo check:* now closed. `Clean/Specs/Poseidon.lean` uses CompPoly's Pratt certificate (`BN254.ScalarField_is_prime`). The repo's `Poseidon.md` is stale on this point.
    - Arities 2–4 are future work.
  - Clean itself is a Lean 4 DSL for AIR circuits with soundness and completeness against Lean specs, and part of the EF zkEVM formal verification project. [intro post](https://blog.zksecurity.xyz/posts/clean)
- ✔ **Verified-zkEVM / EvmAsm** ([Reservoir](https://reservoir.lean-lang.org/@Verified-zkEVM/EvmAsm)) has **no** hash spec. KECCAK256 is only a precompile interface, and the project is a prototype.
- **EF verified-zkevm.org** (A. Hicks, FMBC 2026 invited talk, [abstract](https://drops.dagstuhl.de/storage/01oasics/oasics-vol142-fmbc2026/OASIcs.FMBC.2026.2/OASIcs.FMBC.2026.2.pdf)) is the umbrella project. Watch it for precompile and hash specs.

---

## 5. Gap-closing pass: other provers and ZK-circuit work

### 5.1 Cryptol and SAW

- **Galois `cryptol-specs`** ([repo](https://github.com/GaloisInc/cryptol-specs), BSD-3-Clause, last push 2026-10-05). `Primitive/Keyless/Hash/` holds executable specs:
  - **SHA-2** (all FIPS 180-4 variants), **SHA-3** (SHA3-224/256/384/512, SHAKE128/256) and **SHA-1**, each marked "gold standard" under the repo's [reviewing guidelines](https://github.com/GaloisInc/cryptol-specs/wiki/Reviewing-guidelines).
  - BLAKE2b, BLAKE2s, FNV and MD5 as "proof-of-concept" specs.
  - The SHA-3 README documents Keccak's unusual bit ordering, with conversion helpers (`KeccakBitOrdering.cry`).
  - A SHA-256 FFI version is checked, but not proved, equivalent to the gold-standard spec.
  - No ZK-friendly hashes.
- **AWS-LC verification** ([awslabs/aws-lc-verification](https://github.com/awslabs/aws-lc-verification), Apache-2.0, last push 2026-03).
  - SAW proves AWS-LC's SHA-384 and SHA-512 (`EVP_Digest*`) against Cryptol specs from `cryptol-specs`: on x86 (SandyBridge+), and on aarch64 (Neoverse N1/V1) together with NSym.
  - It also proves HMAC-SHA384 on x86.
  - Coq is used to validate some of the Cryptol specs.
  - Caveats are documented per result, for example `ArmSpecGap`: the Arm proofs use a recursive variant of the spec whose top-level loop is not verified.

### 5.2 ACL2 (Kestrel Institute)

All in [acl2/acl2](https://github.com/acl2/acl2) under a BSD-3 licence.

- **`books/kestrel/crypto/`:**
  - `sha-2/` (SHA-224/256/384/512, with tests)
  - `keccak/` (with the Keccak team's test data)
  - `sha-3/` (connected to the Keccak book)
  - `blake/` (BLAKE-256, BLAKE2b, BLAKE2s and an extended BLAKE2s, with the BLAKE2 KATs)
  - `mimc/` (MiMCSponge, with Semaphore's round constants)
  - an R1CS library (`r1cs/`)
  - RIPEMD-160 appears only as an interface, with no definition.
- **Circuit proofs (`books/kestrel/ethereum/semaphore/`).** Soundness proofs that Semaphore's circom R1CS for MiMCSponge (sizes 1-1, 2-1, 5-1) implies the MiMCSponge spec. There are also gadget proofs (BLAKE2s mixing, 32-bit add, xor and rotate, Montgomery/Edwards conversion) and a Semaphore Pedersen-hash spec with no circuit proof. Authors are Eric Smith and Alessandro Coglio, 2020–21.
- **Zcash (`books/kestrel/zcash/`).** A formalisation of the Sapling **Pedersen hash** (ZPS §5.4.1.7) over Jubjub, with proved bound, image and **injectivity** properties, plus some Sapling gadget proofs (2021).
- **Poseidon (`books/projects/poseidon/`).**
  - A parameterised Poseidon spec by Coglio and McCarthy (Provable, 2024).
  - Instantiations: Aleo's rate 2, 4 and 8 with α = 17 over BLS12-377, and Ingonyama's BN254 t = 3, each with test vectors.
  - Only structural lemmas.
- **Aleo circuits (`books/projects/aleo/vm/circuits/axe/poseidon-rate*.lisp`, 2025).** Soundness: the lifted snarkVM R1CS implies `out = poseidon::hash2(in)`.

### 5.3 Isabelle/HOL and the AFP

- **AFP [`Crypto_Standards`](https://www.isa-afp.org/entries/Crypto_Standards.html)** (A. Whitley, 2023).
  - `FIPS180_4.thy` specifies the whole FIPS 180-4 family: SHA-1, -224, -256, -384, -512, -512/224 and -512/256.
  - It is written to read like the standard and checked against NIST vectors by evaluation.
  - The entry also covers HMAC (FIPS 198-1), PKCS#1 v2.2 and SEC1.
  - Spec only: no implementation proof and no security proof.
- **AFP `RSAPSS`** (2005): a SHA-1 spec used inside RSA-PSS.
- **RIPEMD-160 SPARK verification** (F. Immler, 2011). A functional spec plus proofs of the SPARK verification conditions, i.e. correctness of a SPARK/Ada implementation. It now lives in the Isabelle distribution (`src/HOL/SPARK/Examples/RIPEMD-160/`).
- **Abstract only:** `ADS_Functor` (Merkle trees over an abstract hash), `Isabelle-Solidity` (Keccak-256 assumed injective), `Compressed_Oracles` (quantum random-oracle security).
- **Not found in the AFP:** concrete Keccak/SHA-3, BLAKE2/3, any ZK-friendly hash, sponge or Merkle–Damgård constructions.

### 5.4 Coq/Rocq beyond VST

- **Formal Land Garden** ([formal-land/garden](https://github.com/formal-land/garden), active 2026). This is the most substantial Rocq ZK-hash work.
  - The Halo2 Poseidon gadget used in Zcash Orchard (`P128Pow5T3`, Pallas, t = 3, x⁵, R_F = 8, R_P = 56) has a spec.
  - Per-round chip proofs, and a proof that the Orchard nullifier cell equals `poseidon_hash2 nk rho_old`.
  - Round constants and the MDS matrix are **re-derived inside the kernel from the Grain LFSR**.
  - A Plonky3 Keccak AIR is proved to imply the round computation.
  - An executable RFC 7693 BLAKE2b spec.
  - circomlib's Poseidon, MiMC and Pedersen are translated to Rocq, but nothing is proved about them.
  - No peer-reviewed paper found.
- **Silver Oak** (Google, `project-oak/silveroak`): Coq SHA-256 and HMAC specs, with hardware correctness proofs of the Cava SHA-256 circuit (OpenTitan). Inactive since 2022.
- **hacspec v1 Coq backend:** generated definitions for SHA-1, SHA-256, SHA-512 and SHA-3, with no lemmas. The repo is archived. Its successor, **hax**, has Lean proofs for its SHA-3 example (`examples/sha3`), but no Rocq hash output was found.
- **Veridise Coda** (S&P 2024): circomlib Poseidon and MiMCSponge are **uninterpreted, trusted functions**, so no hash spec.
- **Also seen:** VST's HMAC-DRBG, Jasmin's Coq semantics of the SHA-NI instructions, and `rocq-of-rust`'s executable Keccak-256 model (no proofs).
- **Not found:** Fiat-Crypto, bedrock2, SSProve and CertiCrypt have no hash functions. There is no standalone Coq SHA-3, MiMC or Rescue spec with proofs.

### 5.5 HOL4 and CakeML

Paths below are in [HOL-Theorem-Prover/HOL](https://github.com/HOL-Theorem-Prover/HOL), under `examples/Crypto/`.

- **Keccak** (`Keccak/keccakScript.sml`).
  - Defines Keccak-p, the sponge with pad10*1, SHA3-224/256/384/512 and Keccak-256.
  - `Keccak_256_w64_thm` proves an optimised 64-bit-lane Keccak-256 equal to the spec. Its last `cheat`s (unproved steps) were removed on 2026-09-09.
  - This is a direct precedent for our fast-equals-reference discipline.
- **Other hashes in the same tree:**
  - `SHA-2/` (SHA-256 only, evaluable, with test-vector theorems; 2024–25)
  - `RIPEMD/` (RIPEMD-160, 2025)
  - `MD/` (shared Merkle–Damgård padding)
  - `MD5/` and `SHA-1/`
  - a `pedersenCommitment` theory (a commitment scheme, not a hash; not examined further)
- **CakeML:** a verified MD5 implementation translated from the HOL4 spec. It is the only verified hash implementation found in CakeML.
- **Verifereum** (a HOL4 EVM spec): specifies the EIP-152 BLAKE2b F function and uses HOL4's SHA-256 and RIPEMD-160 for the precompiles.

### 5.6 More Lean 4 work

- **LNSym** ([leanprover/LNSym](https://github.com/leanprover/LNSym), AWS, Apache-2.0, last push 2026-07): an Armv8 symbolic simulator in Lean. It proves AWS-LC's Arm SHA-512 block code against `Specs/SHA512.lean`.
- **Reilabs:**
  - The gnark→Lean extractor and `gnark-lean-demo` prove BN254 Poseidon circuits (t = 2, 3) equivalent to a textbook permutation spec. They are reused in Worldcoin's `semaphore-mtb` and in Light Protocol.
  - **Lampe** (Noir→Lean): proves the Noir stdlib Poseidon2 *sponge* against a Lean spec, with the BN254 t = 4 permutation as a trusted builtin. It also proves the Noir **Pedersen** hash and commitment (Grumpkin) against a Lean spec (2026).
- **Other Poseidon specs in Lean:**
  - `argumentcomputer/Poseidon.lean` (Lurk): executable Poseidon over BN254 and BLS12-381, no theorems.
  - CatCrypt (`spitters/catcrypt-compiler`): Poseidon2 and Poseidon specs used in a verified compiler; a pre-release prototype.
- **Verified-zkEVM specs:**
  - `clean` (BLAKE3, Keccak-256, SHA-256, Poseidon).
  - ArkLib (Poseidon2, KoalaBear).
  - VCVio (pure-Lean Keccak, SHAKE and SHA-3).
  - These are already listed in `ROADMAP.md` §1.
- **Nethermind CertiPlonk:** a blog post (2026-07-03) claims a Lean Poseidon2 was proved equal to an independent reference implementation. No Poseidon2 files were found in the repos, so this is unconfirmed.

### 5.7 ZK-friendly hashes: overall picture

| Result type | Artifacts |
|---|---|
| Circuit proved **sound and complete** against a spec | Clean: circomlib Poseidon, BN254, arity 1 |
| Circuit proved **sound** against a spec | Kestrel: Aleo Poseidon (BLS12-377) and Semaphore MiMCSponge (BN254); Garden: Halo2/Orchard Poseidon (Pallas); Reilabs: gnark Poseidon (BN254); Lampe: Noir Poseidon2 sponge and Pedersen |
| Spec only | ArkLib Poseidon2; Lurk Poseidon.lean; Kestrel Poseidon library and Zcash Pedersen (with injectivity); AMO-Lean Poseidon2 (unfinished) |
| Determinism or underconstraint checks only (no functional spec) | Picus (circomlib Poseidon, MiMC, Pedersen benchmarks), Ecne, RISC Zero + Picus (Keccak accelerator), CIVER |
| Hash treated as a trusted black box | Coda (Poseidon, MiMCSponge), several Isabelle developments |

- No artifact proves optimized ≡ textbook Poseidon for all inputs. Clean only tests it.
- No machine-checked spec of Rescue, Rescue-Prime, RPO, Anemoi, Griffin, Monolith, Tip5 or Reinforced Concrete was found in any prover.

---

## 6. Remaining gaps and open questions

**Still not found anywhere:**
- Rescue, Rescue-Prime and RPO, Anemoi, Griffin, Monolith, Tip5, Reinforced Concrete.
- A reusable, multi-instance Poseidon or Poseidon2 library with proofs. All existing work fixes one or two instances.
- A proof that optimized (sparse-matrix) Poseidon equals the textbook algorithm.
- A verified Poseidon2 *permutation* circuit, as far as anything could be confirmed.
- A BLAKE3 spec outside Lean and Verified-zkEVM.

**Search coverage caveat:** GitHub code search was rate-limited partway through the gap-closing pass. The Coq and Isabelle searches for the newer ZK hashes rest on web search plus partial code search, so small repos may have been missed.

**Open questions:**
1. Are the SymCrypt Lean FIPS 202 and 180-4 specs public and reusable (repo, licence, test-vector validation)?
2. Is completeness proved for the zkLean Keccak circuit? (Its location is now known; see §2.2.)
3. Can the hax Lean backend turn libcrux's hacspec SHA-2, SHA-3 and BLAKE2 specs into Lean specs? hax already has Lean SHA-3 proofs in its examples.
4. How do the independent Lean Keccak specs relate? There are now at least eight: SymCrypt, zkLean, Nethermind LeanCrypto, Axiom openvm-fv, Doussot, VCVio, Clean and hax. A proved equivalence between them would be valuable in its own right.
5. Is CertiPlonk's Poseidon2 equivalence claim backed by public code, and for which field and width?

---

## 7. Reliability ranking of sources

1. **Peer-reviewed, machine-checked, stable:**
   - Appel TOPLAS 2015
   - Beringer et al. USENIX Sec 2015
   - Almeida et al. CCS 2019
   - HACL* (CCS 2017/2020)
2. **Released, maintained prover libraries:**
   - HOL4 `keccak` (with `Keccak_256_w64_thm`)
   - HACL* F* specs
   - AFP `Crypto_Standards`
   - Galois `cryptol-specs` gold-standard SHA-2 and SHA-3
   - Kestrel ACL2 crypto books
   - AWS-LC SAW proofs
3. **Strong recent Lean work, not yet peer-reviewed:**
   - SymCrypt/Aeneas (arXiv 2026)
   - Axiom openvm-fv (axiom-audited)
   - LNSym SHA-512
   - Clean Poseidon (sound and complete)
4. **Active research repos without papers:** Formal Land Garden, Reilabs Lampe, Kestrel Poseidon and Aleo circuits.
5. **Vendor or self-reported:** the Cryspen FMCP slides, the libjade README, the Galois zkLean article, the zkSecurity Clean posts, the CertiPlonk Poseidon2 claim.
6. **Experimental, incomplete or definitions-only:**
   - ePrint 2024/1880
   - Reilabs gnark-lean-demo
   - AMO-Lean
   - Nethermind LeanCrypto (definitions only)
   - Lurk Poseidon.lean
   - CatCrypt

**Trust-base reminder:**
- Every implementation proof trusts something: the CompCert x86 model, KaRaMeL, the Jasmin compiler, Aeneas plus intrinsic axioms, or circuit extractors.
- The security proofs are conditional: the HMAC result assumes a PRF compression function, and the SHA-3 result assumes an ideal permutation.
- A spec is only as good as its audit against the standard. Prefer specs that are cross-checked against NIST/KAT test vectors and that come with proved internal properties.

---

## 8. Implications for `hash-specs`

- **Extra independent oracles exist for differential testing.** Cryptol's gold-standard SHA-2 and SHA-3 specs are executable through the Cryptol interpreter, with a code lineage independent of the Rust crates. ACL2's books are executable too, with test suites for SHA-2, Keccak, BLAKE2, MiMCSponge and Poseidon. Either could be added to `ROADMAP.md` §4.2 as a spec-level oracle.
- **Precedents worth copying:**
  - openvm-fv's CI axiom audit, which forbids `native_decide` and `bv_decide`
  - HOL4's proof that optimized Keccak-256 equals the spec, the same shape as our `Equiv` theorems
  - Garden's in-kernel re-derivation of Poseidon constants from the Grain LFSR, matching "constants are theorems, not trust"
  - Kestrel's parameterised Poseidon spec with per-ecosystem instantiations, matching our explicit instance naming
- **Where the project adds the most:**
  - a reusable, multi-instance Poseidon and Poseidon2 library
  - the first proof that optimized Poseidon equals textbook Poseidon
  - Rescue-Prime and RPO, which nobody has specified
  - one canonical Lean Keccak to replace the eight independent ones
- **Cross-validation sources for test vectors:** Kestrel's Aleo and Ingonyama Poseidon tests and its Semaphore MiMCSponge tests are BSD-3, so they can be vendored with attribution. Check each file's licence anyway (see the roadmap's licence risk).

