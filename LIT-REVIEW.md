# Literature Review: Formal Specifications of Hash Functions

*Compiled 2026-10-11 with a deep-research workflow: 5 search angles, 21 sources fetched, 94 claims extracted, 25 claims adversarially verified by 3-agent voting (24 confirmed, 1 refuted).*

**How to read this:**
- Sections 1–3 hold claims that survived 3-vote adversarial verification (a claim is dropped if 2 of 3 voters refute it).
- Section 4 lists claims taken from primary sources that the verification pass did not reach because of budget. Treat them as well-sourced leads, not confirmed facts.
- Section 5 lists known gaps.

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
| Keccak-256 / SHA-256 | Nethermind LeanCrypto; Axiom openvm-fv | **Lean 4** | Used in ZK-circuit verification (§4) |
| BLAKE2 | HACL*, libcrux | F*, hacspec | Industrial |
| Poseidon | zkSecurity/Clean (circomlib, arity 1); reilabs demo | **Lean 4** | Early, narrow (§3–4) |
| Poseidon2 | AMO-Lean (BN254, t=3) | Lean 4 | Unfinished (12 `sorry`) |
| BLAKE3, Rescue, MiMC, Pedersen | **None found** | — | Gap |

**Bottom line for a Lean 4 hash-spec effort:**
- For SHA-2 and SHA-3, the existing references are Coq, EasyCrypt and F*. The newest and most complete Lean 4 specs are the SymCrypt/Aeneas FIPS 202 and FIPS 180-4 specs, the Nethermind LeanCrypto Keccak-256, and the Axiom openvm-fv Keccak and SHA-256 specs.
- ZK-friendly hashes are essentially unspecified in any prover beyond small Lean 4 Poseidon experiments. That is the main open space.

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
    - **Refuted 0–3:** the claim that this circuit lives in the `GaloisInc/zkLean` repo. Its actual location is unconfirmed.

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

These were extracted from fetched primary sources but were not put through the 3-vote verification pass. Several are probably the most directly useful items for a Lean 4 ZK hash-spec project.

- **Nethermind: Keccak-256 in Lean (LeanCrypto) and Scroll Halo2 circuit.** [blog](https://www.nethermind.io/blog/formal-verification-of-halo2-circuits-in-lean) · [NethermindEth/LeanCrypto](https://github.com/NethermindEth/LeanCrypto)
  - A hand-written mathematical Keccak-256 spec in Lean 4.
  - The Halva tool extracts Halo2 constraints into Lean.
  - Proved that most Scroll Keccak circuit constraints imply the spec's absorb and squeeze phases (not full correctness).
  - Found an **underconstraint bug**: `is_final` could be set on an intermediate row to produce arbitrary output. A PoC is at `NethermindEth/scroll-keccak256-PoC`.
- **Axiom: OpenVM Keccak-f[1600] and SHA-256 circuits in Lean.** [blog](https://axiom.xyz/blog/fv-keccak-sha2) · [openvm-org/openvm-fv](https://github.com/openvm-org/openvm-fv)
  - Lean reference specs hand-written from FIPS 202 and FIPS 180-4 and audited by hand against the standards.
  - Proves that constraint satisfaction implies the reference hash. This is soundness; completeness is not discussed.
  - Proofs were generated by an agentic AI formalizer.
  - The TCB includes the circuit-to-Lean extraction and the specs.
- **zkSecurity: Poseidon in Clean.** [blog](https://blog.zksecurity.xyz/posts/poseidon-clean/) · [Verified-zkEVM/clean](https://github.com/Verified-zkEVM/clean)
  - Soundness **and completeness** of a hand-modelled circomlib optimized Poseidon, for arity 1 (t=2) over BN254, against `Clean/Specs/PoseidonOptimized.lean`.
  - The repo also has a textbook spec, `Clean/Specs/Poseidon.lean`.
  - *Caveats:*
    - The two Poseidon specs are not proved equal; they are only cross-tested, including against circomlibjs vectors.
    - The Circom source is not parsed mechanically.
    - One `sorry` remained for the primality of the BN254 prime, pending a CompPoly certificate.
    - Arities 2–4 are future work.
  - Clean itself is a Lean 4 DSL for AIR circuits with soundness and completeness against Lean specs, and part of the EF zkEVM formal verification project. [intro post](https://blog.zksecurity.xyz/posts/clean)
- **Verified-zkEVM / EvmAsm** ([Reservoir](https://reservoir.lean-lang.org/@Verified-zkEVM/EvmAsm)) has **no** hash spec. KECCAK256 is only a precompile interface, and the project is a prototype.
- **EF verified-zkevm.org** (A. Hicks, FMBC 2026 invited talk, [abstract](https://drops.dagstuhl.de/storage/01oasics/oasics-vol142-fmbc2026/OASIcs.FMBC.2026.2/OASIcs.FMBC.2026.2.pdf)) is the umbrella project. Watch it for precompile and hash specs.

---

## 5. Gaps and things this run did not cover

**No verified spec found in any prover for:**
- BLAKE3
- Rescue / Rescue-Prime
- MiMC
- Pedersen hash
- Poseidon outside Lean

**Not confirmed by this run, but likely to exist; check them next (author's knowledge, unverified):**
- **Cryptol / SAW:** Galois's `cryptol-specs` repo (SHA-2, SHA-3/Keccak, BLAKE2 and others) and SAW proofs, for example AWS-LC SHA-2.
- **ACL2:** Kestrel's crypto books (SHA-2, Keccak/SHA-3, possibly BLAKE2s).
- **Isabelle AFP:** no hash entries surfaced. Search the AFP directly.
- **Coq beyond VST:** for example Fiat-Crypto, which covers field arithmetic rather than hashes, and any Poseidon or Rescue work in Coq.
- **ZK-circuit verification groups:** Veridise (Picus, Coda), CertiPlonk, ArkLib, and other Lean ZK groups. These may hold Poseidon, MiMC or Rescue specs.

**Open questions:**
1. Are the SymCrypt Lean FIPS 202 and 180-4 specs public and reusable (repo, licence, test-vector validation)?
2. Where does the zkLean Keccak proof live, and is completeness proved?
3. Can the hax Lean backend turn libcrux's hacspec SHA-2, SHA-3 and BLAKE2 specs into Lean specs? That would give a cross-prover link to the F* and EasyCrypt work.
4. How do the independent Lean Keccak specs relate? There are at least five: SymCrypt, zkLean, Nethermind LeanCrypto, Axiom openvm-fv and Doussot. A proved equivalence between them would be valuable in its own right.

---

## 6. Reliability ranking of sources

1. **Peer-reviewed, machine-checked, stable:**
   - Appel TOPLAS 2015
   - Beringer et al. USENIX Sec 2015
   - Almeida et al. CCS 2019
   - HACL* (CCS 2017/2020)
2. **Released prover libraries:** the HOL4 `keccak` theory and the HACL* F* specs.
3. **Strong recent Lean work, not yet peer-reviewed:** SymCrypt/Aeneas (arXiv 2026), Axiom openvm-fv, Nethermind LeanCrypto.
4. **Vendor or self-reported:** the Cryspen FMCP slides, the libjade README, the Galois zkLean article, the zkSecurity Clean posts.
5. **Experimental or incomplete:** ePrint 2024/1880, reilabs gnark-lean-demo, AMO-Lean.

**Trust-base reminder:**
- Every implementation proof trusts something: the CompCert x86 model, KaRaMeL, the Jasmin compiler, Aeneas plus intrinsic axioms, or circuit extractors.
- The security proofs are conditional: the HMAC result assumes a PRF compression function, and the SHA-3 result assumes an ideal permutation.
- A spec is only as good as its audit against the standard. Prefer specs that are cross-checked against NIST/KAT test vectors and that come with proved internal properties.
