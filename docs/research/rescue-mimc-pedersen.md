> **Provenance.** Research notes compiled on 2026-10-12 by Claude Code research agents (see `AI_USE.md`) for Phases 4–5, from the pinned primary sources listed below. Paths such as `scratchpad/scripts/…` and `scratchpad/dl/…` refer to the agents' working files (Python checks and cloned sources), which are not vendored. Where these notes and the Lean specifications disagree, the Lean docstrings, which cite the primary sources, are authoritative.

# Phase 5 research: Rescue-Prime, RPO, MiMC, Pedersen (BabyJubJub, Grumpkin)

Research date: 2026-10-12. No repo files were edited. Everything below comes from primary sources: papers, reference code and the implementing repos. The commit SHA is recorded for each source. Items marked **[verified]** were re-derived or recomputed independently by me in scratch scripts (Python with hashlib SHAKE256 and hand-written BLAKE3, or circomlibjs run under node); they are not just copied. Scratch scripts are in `scratchpad/scripts/`: `rp.py`, `rpo_consts.py`, `rpo_check.py`, `noirped.py`, `c1.mjs`/`c2.mjs`/`c3.mjs`.

Source pins:

| Source | Repo / URL | Commit / version | Licence |
|---|---|---|---|
| Rescue-Prime SoK | eprint 2020/1143 (Szepieniec, Ashur, Dhooghe) | PDF (v. on eprint, fetched via web.archive) | — |
| Rescue-Prime reference Sage | github.com/KULeuven-COSIC/Marvellous `rescue_prime.sage` | b265d9a98d85c4f856a0ba2590045ac03dc241c2 (2021-04-14) | MIT |
| stark-anatomy Rescue-Prime instance | github.com/aszepieniec/stark-anatomy `code/rescue_prime.py`, `code/test_rescue_prime.py` | cae79160fd7bf26312ef322b90cf1d0fdd9c5e5c | Apache-2.0 |
| RPO paper | eprint 2022/1577 (Ashur, Kindi, Meier, Szepieniec, Threadbare), dated 14 Nov 2022 | — | — |
| RPO reference Sage | github.com/ASDiscreteMathematics/rpo `reference_implementation/rescue_prime_optimized.sage` | b2889d6ee6368588f621b909dfcf653e8b66df0e | Apache-2.0 |
| miden-crypto (archived repo) | github.com/0xMiden/crypto (formerly 0xPolygonMiden/crypto; **archived**) `miden-crypto/src/hash/algebraic_sponge/...` | 475092a8476bf4c806424579e5d9225b12941c1a (crate v0.29.0) | MIT OR Apache-2.0 |
| miden-crypto (current home) | github.com/0xMiden/miden-vm `crates/crypto/src/hash/algebraic_sponge/...` | 4016cf0532659da5368c97859ff869500c650ffb (crate v1.0.0 in tree; crates.io latest 0.35.0) | MIT OR Apache-2.0 |
| Winterfell | github.com/facebook/winterfell `crypto/src/hash/rescue/` | 2f78ee9bf667a561bdfcdfa68668d0f9b18b8315 (winter-crypto 0.13.1) | MIT |
| MiMC paper | eprint 2016/492 (Albrecht, Grassi, Rechberger, Roy, Tiessen), ASIACRYPT 2016 | — | — |
| circomlib | github.com/iden3/circomlib | 35e54ea21da3e8762557234298dbb553c175ea8d | package.json says LGPL-3.0, file headers say GPL-3.0 (inconsistent) |
| circomlibjs | github.com/iden3/circomlib | 48b3ab37013c5ed21e9ff8a80a5b010795c97094; npm 0.1.7 used for execution | GPL-3.0 (package.json; GitHub API reports none) |
| iden3 docs | github.com/iden3/iden3-docs `source/docs/Pedersen-Hash.pdf`, `Baby-Jubjub.pdf` | 3ae327e53358e0092f61877ca0bff64c22212975 | — |
| Noir | github.com/noir-lang/noir | 5662e904adeabff599df2c74b26b87b67e3241b3 (1.0.0-rc.4) | MIT OR Apache-2.0 |
| barretenberg | github.com/AztecProtocol/aztec-packages `barretenberg/cpp/src/barretenberg/...` | bb15fcbbe969f11a892272715fe59f0976b086ca | Apache-2.0 |
| Lampe | github.com/reilabs/lampe | 13c210ef75723295f015657d7e25618f794ed62a (Lean v4.29.1, Mathlib v4.29.1) | Apache-2.0 |
| Mathlib (local) | `.lake/packages/mathlib` | 5ed2965256430c3649e86755f9576b54eca72435 (2026-09-15; repo toolchain v4.34.0) | Apache-2.0 |

---

## 1. Rescue-Prime (eprint 2020/1143)

### 1.1 Paper structure (section and algorithm numbers)
- §2.1 Parameters: primary tuple (p, m, c_p, s). p is prime with ≥ 32 bits; m > 1 is the state width; c_p is the capacity, r_p = m − c_p the rate; 80 ≤ s ≤ 512. Derived: α, α⁻¹, MDS M ∈ F_p^{m×m}, N rounds, and 2mN round constants C_i.
- §2.2 The hash function, including Fig. 1.
  - **Algorithm 1** `rescue_prime_hash` (no padding):
    - The state starts at all-zero.
    - Absorb adds (`+=`) each block of r_p elements into state[0..r_p), then applies the permutation.
    - Squeeze outputs state[0..r_p). Only one squeeze is allowed (the output is at most r_p elements).
  - **Algorithm 2** `rescue_prime_wrapper` (padding): append a single 1, then 0s up to a multiple of r_p.
  - Truncation to n < r_p elements is allowed.
- §2.3 Rescue-XLIX permutation, Fig. 2 and **Algorithm 3**. Each of the N rounds is:
  1. x ↦ x^α on every element
  2. state ← M·state
  3. add C[2im + j]
  4. x ↦ x^{α⁻¹} on every element
  5. state ← M·state
  6. add C[2im + m + j]

  (This order matches the task description: S-box, MDS, constants, inverse S-box, MDS, constants.)
- §2.4 Selecting the parameters.
  - **Algorithm 4**, MDS:
    - Let g be the smallest primitive element of F_p, found by trying 2, 3, ….
    - Form V = [g^{ij}] for i < m and j < 2m, and bring it to reduced row-echelon form (I | Mᵀ).
    - Then MDS = (right half)ᵀ. Sage: `V.echelon_form()[:, m:].transpose()`.
  - **Algorithm 5**, round constants:
    - `bytes_per_int = ceil(|p|/8) + 1`, where |p| is the bit length of p.
    - Expand the ASCII seed `"Rescue-XLIX(%i,%i,%i,%i)" % (p, m, capacity, security_level)` with SHAKE256 to `bytes_per_int·2mN` bytes.
    - Each chunk is read **little-endian** and reduced mod p.
- §2.5:
  - **Algorithm 6** sets α to the smallest integer ≥ 3 coprime to p − 1, and α⁻¹ = α^{-1} mod (p − 1).
  - **Algorithm 7** sets the number of rounds:
    - dcon(N) = ⌊0.5(α−1)m(N−1) + 2⌋ and v(N) = m(N−1) + r_p.
    - ℓ₁ is the smallest N in 1..24 with binom(v + dcon, v)² > 2^s.
    - N = ⌈1.5·max(5, ℓ₁)⌉.
- §3 lists the changes from original Rescue: §3.1 flipped S-box order, §3.2 simplified constants, §3.3 reduced margin.
- §4 lists sanctioned deviations: §4.1 small fields (Algorithm 8), **§4.2 alternate MDS matrices**, **§4.3 omission of padding** (for fixed-length inputs), §4.4 algebraically dependent constants, §4.5 n > r_p (Algorithms 9 and 10, DEC and sponge).
- **The paper contains no test vectors.**

The reference Sage file (Marvellous `rescue_prime.sage`) is the paper's Algorithms 1–7 verbatim. It also contains `rescue_prime_DEC` and `rescue_prime_sponge` (multi-squeeze), and a `get_number_of_rounds1` that also accounts for the differential bound ℓ₀. Note: the deployed `get_number_of_rounds` is the Gröbner-only version, as in the paper. `aszepieniec/rescue-prime` returns 404, so the canonical code is in Marvellous.

### 1.2 Concrete instances with vectors
1. **stark-anatomy instance** (Apache-2.0). This is the best available KAT source for a *standard* instance.
   - Parameters: p = 407·2^119 + 1 = 270497897142230380135924736767050121217, m = 2, c = 1, r = 1, s = 128, α = 3, α⁻¹ = 180331931428153586757283157844700080811, N = 27.
   - MDS = [[p−3, 4], [p−12, 13]], i.e. [[270497897142230380135924736767050121214, 4], [270497897142230380135924736767050121205, 13]].
   - The 108 round constants are hard-coded.
   - `hash(x)` sets state = [x, 0], applies the permutation and returns state[0]. That is fixed-length absorption with no padding (§4.3).
   - KATs from `code/test_rescue_prime.py`:
     - `hash(1) = 244180265933090377212304188905974087294`
     - `hash(57322816861100832358702415967512842988) = 89633745865384635541695204788332415101`
   - **[verified]**: my independent Python implementation of Algorithms 4, 5, 6 and 7 reproduces this instance from the paper's algorithms. It gives α and α⁻¹, N = 27, the MDS matrix exactly, and all 108 constants from SHAKE256 of `Rescue-XLIX(270497897142230380135924736767050121217,2,1,128)`. It also reproduces `hash(1)`. This is a good small KAT that exercises *every* derivation algorithm. The constant-derivation chain (SHAKE256 → constants) can reuse the repo's existing SHAKE256.
2. **Winterfell `Rp64_256`** (winter-crypto, MIT) is a *non-standard Rescue-Prime variant* with these deviations, documented in the code:
   - 7 rounds instead of 8.
   - The RPO circulant MDS (first row [7,23,8,26,13,10,9,7,6,22,21,8]) instead of the Vandermonde matrix (§4.2).
   - Capacity at positions 0..3 and rate at 4..11, with the digest at 4..7.
   - capacity[0] = number of elements, followed by zero padding only.
   - The round order is the standard Rescue-Prime one (sbox, MDS, +ARK1, inv-sbox, MDS, +ARK2).
   - The doc comment says the constants were "computed using algorithm 5". However, **I could not reproduce them**. I tried the SHAKE256 seeds `Rescue-XLIX/Rescue-Prime/RPO/Rescue(p,m,c,s)` for m ∈ {8,12,16}, c ∈ 1..8, s in common values, 8/9/10/16-byte chunks and both endiannesses, and none matched. Provenance is unknown.
   - The repo has no KATs for it. **Not recommended as an oracle** for standard Rescue-Prime.
   - `Rp62_248` (62-bit field) and `RpJive64_256` also exist.
3. **matter-labs `rescue_poseidon`** (crates.io 0.32.11, MIT OR Apache-2.0; source in matter-labs/zksync-crypto, older repo matter-labs/rescue-poseidon @8f38e236). Its `rescue_prime/params.rs` implements Algorithms 5, 6 and 7 for BN254 with **security_level = 80** (hard-coded), using SHAKE256 and the same seed format. Caveats:
   - `compute_round_constants` zips 2mN constants into only `n` arrays of WIDTH, so it may use only the first m·N constants. This needs checking before use.
   - The MDS comes from `compute_mds_matrix_for_rescue` (not checked against Algorithm 4).
   - Treat it as a *candidate* BN254 oracle of unconfirmed conformance.
4. Neptune `twenty-first` (GPL-2.0) historically had Rescue-Prime Regular/XLIX code. It is no longer in the HEAD tree (only Tip5 remains). Not pursued.

**Recommendation.** Build the Rescue-Prime reference over generic (p, m, c, s) with Algorithms 3–7. Prove the stark-anatomy instance's MDS and constants equal the computed values (this mirrors the Poseidon Grain-LFSR approach), and use `hash(1)` and the second vector as `decide +kernel` KATs. α⁻¹ is a ~128-bit exponent with N = 27, so kernel evaluation is feasible but should be measured. For a large field there is no external standard-instance vector. Self-generated vectors from the reference Sage (`rescue_prime_parameters(p,m,c,s)` + `rescue_prime_wrapper`) are the fallback, which would need Sage.

---

## 2. RPO, Rescue Prime Optimized (eprint 2022/1577)

### 2.1 Paper (sections)
The paper is a delta against Rescue-Prime; the reference Sage is ASDiscreteMathematics/rpo.
- §2.1 Integer parameters, Table 1:
  - p = 2^64 − 2^32 + 1 (Goldilocks), N = 7, α = 7, α⁻¹ = 10540996611094048183.
  - λ = 128: m = 12, r = 8, c = 4.
  - λ = 160: m = 16, r = 10, c = 6.
- §2.2 Round constants:
  - Seed: the ASCII string `"RPO(%i,%i,%i,%i)"` with (p, m, c, λ).
  - Expand with SHAKE256 to 9·2·N·m bytes.
  - Each 9-byte chunk is read little-endian and reduced mod p.
  - This gives 2mN = 168 constants for m = 12.
  - Round i uses C[24i .. 24i+12) in the first half and C[24i+12 .. 24i+24) in the second half.
- §2.3 MDS is circulant with first row [7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8] (m = 12). For m = 16 it is [256, 2, 1073741824, 2048, 16777216, 128, 8, 16, 524288, 4194304, 1, 268435456, 1, 1024, 2, 8192].
  - Sage's `matrix.circulant(v)` gives M[i][j] = v[(j − i) mod m]. Row 1 is [8, 7, 23, …], i.e. each row is the previous one rotated right.
- §2.4 New round order. Each half-round is **MDS → add constants → S-box**. The full round is:

  `MDS; +C_first; x^7; MDS; +C_second; x^{α⁻¹}`

  This differs from Rescue-Prime, which puts the S-box first.
- §2.5 Padding (paper):
  - Zero-length input is not allowed.
  - If len ≡ 0 mod r: capacity is all 0 and there is no padding.
  - Otherwise: capacity[0] = 1, and append 1 then 0s up to a multiple of r.
- §2.6 **Overwrite mode**: absorption is s[j] ← i[j], not +=.
- §2.7 Indexing: capacity at indices 0..c−1 and rate at c..m−1. The digest is s[c .. c + r/2).
- §3 Test vectors (§3.1 is the 128-bit instance): inputs [0], [0,1], …, [0..18]. First entries:
  - `[0] -> [1502364727743950833, 5880949717274681448, 162790463902224431, 6901340476773664264]`
  - `[0 1] -> [7478710183745780580, 3308077307559720969, 3383561985796182409, 17205078494700259815]`
  - `[0..7] -> [2242391899857912644, 12689382052053305418, 235236990017815546, 5046143039268215739]`
  - The full list is in the paper §3.1 and is regenerable with `print_test_vectors(128)` in the Sage.
- §4 Motivation: §4.1 circulant MDS, with Karatsuba and NTT multiplication (Algorithm 1 = NTT circulant multiply); §4.2 reduced rounds; §4.3 order for folding; §4.4 stack-VM indexing and overwrite; §4.5 padding.

**[verified]**
- `SHAKE256("RPO(18446744069414584321,12,4,128)")`, chunked into 9-byte little-endian integers mod p, gives exactly miden-crypto's `ARK1` (84 values) and `ARK2` (84 values).
- The circulant row and α⁻¹ match.
- My Python permutation with the paper's sponge reproduces paper vectors [0], [0,1] and [0..7].

### 2.2 Miden `Rpo256` (miden-crypto) differs from the paper's sponge
The permutation is identical to the paper's, with the same round order: `apply_mds; add ARK1[r]; sbox x^7; apply_mds; add ARK2[r]; inv_sbox`. The sponge and layout differ, as documented in `rescue/rpo/mod.rs`, "padding rule follows eprint 2023/1045" (the RPX paper):

- **State layout** (≥ v0.21.0, CHANGELOG: "[BREAKING] Changed sponge state layout from `[CAPACITY, RATE1, RATE0]` (BE) to `[RATE0, RATE1, CAPACITY]` (LE) (#755)"):
  - rate = state[0..8): RATE0 = 0..4, RATE1 = 4..8
  - capacity = state[8..12)
  - digest = state[0..4)
  - Before 0.21 the layout was capacity 0..3, rate 4..11, digest 4..7, as in the paper and Winterfell. **Vectors changed at 0.21**, so pin a version.
- `hash_elements(elems)`:
  - Initial state is 0, then set state[8] = (len mod 8).
  - Overwrite-absorb 8 at a time, permuting after each full block.
  - If a partial block remains, fill the rest of the rate with 0 and permute.
  - Return state[0..4).
  - **Empty input returns [0,0,0,0] with no permutation.**
  - No 1 is appended. Domain separation comes only from len mod 8 in capacity[0].
  - The paper's "multiple-of-r means capacity = 0" case coincides, since len mod 8 = 0 there.
- `merge([w0, w1])`: state = w0‖w1‖0000, permute once, return state[0..4). This equals `hash_elements` of the 8 elements (len mod 8 = 0).
- `merge_in_domain(values, d)`: like merge, but state[9] = d.
- `hash_elements_in_domain(e, d)`: state[9] = d, then the `hash_elements` path.
  - In the miden-vm HEAD version (1.0.0 in tree), when e is empty and d ≠ 0 it sets state[10] = 1 and permutes. This was added after the archived 0.29.0.
- `hash(bytes)`:
  - state[8] = 8 + (num_field_elems mod 8), where num_field_elems = ⌈len/7⌉.
  - Bytes are split into 7-byte chunks, each read as u64 little-endian. The last chunk is padded with a single 0x01 byte after the data, then zeros (into an 8-byte buffer).
  - Elements are overwrite-absorbed. A partial final block is zero-filled and permuted.
  - **Empty bytes**: archived v0.29 returns [0,0,0,0]. **miden-vm HEAD** sets state[0] = 1, then permutes and returns the digest. **Behaviour changed**, so pin the version.

**Miden KATs.** `rescue/rpo/tests.rs` `EXPECTED[19]` gives `hash_elements([0..i])` for i = 0..18 with the new layout:
- `[0] -> [8563248028282119176, 14757918088501470722, 14042820149444308297, 7607140247535155355]`
- `[0..18] -> [17273934282489765074, 8007352780590012415, 16690624932024962846, 8137543572359747206]`

These vectors are identical in archived 0.29.0 and miden-vm HEAD. They are cross-checked by `rescue/rpo/generate_test_vectors.py`, a standalone Python port that I ran: "ALL 19 TEST VECTORS MATCH". **[verified]** with my own Python too.

**Rust oracles for RPO**
- `miden-crypto` (crates.io 0.35.0, MIT OR Apache-2.0; repository is now 0xMiden/miden-vm `crates/crypto`). This is the production implementation.
  - It is not independent of the paper authors: Threadbare and Kindi are co-authors.
  - It is independent of our Lean code, so it is fine as a differential oracle.
  - For the paper sponge, the independent check is the Sage reference.
- `winter-crypto` has **no RPO**. Its `Rp64_256` is the Rescue-Prime variant above (different constants and round order), so it is not an RPO oracle.
- Plonky3 integration exists inside miden-crypto (`p3_symmetric` wrappers). That is the same code, not independent.

**Recommendation.** Specify:
- `RPO.permutation` over generic (m, row, constants) with the §2.2 constant derivation proved, as for Poseidon.
- `RPO.paperHash` (paper §2.5–2.7 sponge, capacity-first layout, paper §3.1 KATs).
- `Miden.Rpo256.{hashElements, merge, mergeInDomain, hashElementsInDomain, hashBytes}` at a pinned miden-crypto version, with the rate-first layout and the `EXPECTED` KATs.

The x^{α⁻¹} map with a 64-bit exponent is cheap in the kernel. RPX (eprint 2023/1045, also in miden-crypto `rescue/rpx`) is a natural follow-on but out of scope.

---

## 3. MiMC

### 3.1 Paper (eprint 2016/492, ASIACRYPT 2016)
- §2.1 Block cipher.
  - **MiMC-n/n**: F_i(x) = (x ⊕ k ⊕ c_i)^3, with "c₀ = c_r = 0" (sic). Ciphertext E_k(x) = (F_{r−1} ∘ … ∘ F_0)(x) ⊕ k, with r = ⌈n / log₂3⌉ rounds and random constants.
  - **MiMC-2n/n (Feistel)**: x_L‖x_R ← x_R ⊕ (x_L ⊕ k ⊕ c_i)^3 ‖ x_L. The first and last round constants are 0, and the last round has no swap. It uses r' = 2r rounds.
- §2.2 Permutation: key = 0.
- §2.3 MiMCHash: sponge over MiMC-n/n with "padding according to the sponge specification".
- §5.1 Prime fields: MiMC-p/p requires gcd(3, p − 1) = 1 and r = ⌈log p / log₂ 3⌉. MiMC-2p/p uses double the rounds.
- §5.3 Different round functions, i.e. other exponents.
- For BN254 Fr, gcd(3, p − 1) = 3, so **x³ is not a permutation**. circomlib uses x⁵ (gcd 1) and x⁷ (gcd 1) (**[verified]**). The round counts follow the §5.1 formula with the exponent changed: ⌈log₅ p⌉ = 110, so 220 Feistel rounds, and ⌈log₇ p⌉ = 91. These are §5.3-style variants, so the paper's x³ instance is not what is deployed.

### 3.2 circomlib MiMCSponge (BN254 Fr, p = 21888242871839275222246405745257275088548364400416034343698204186575808495617)
Sources: `circuits/mimcsponge.circom` (circomlib @35e54ea) and `src/mimcsponge.js` (circomlibjs @48b3ab3).

**Constants** (`getConstants`). Note the `seed` argument is ignored and the constant `SEED` is always used:
```js
let c = keccak_256(SEED);            // SEED = "mimcsponge", UTF-8 bytes; c is 32 raw bytes
for (let i=1; i<nRounds; i++) {
    c = keccak_256(c);               // hash the previous 32-byte DIGEST (raw bytes, not hex text)
    cts[i] = F.e("0x" + bytesToHex(c));   // big-endian integer, reduced mod p
}
cts[0] = F.e(0);
cts[cts.length - 1] = F.e(0);        // last (219) overwritten with 0
```
- The hash is Keccak-256 (Ethereum, 0x01 padding), not SHA3-256.
- The integer is big-endian, reduced mod p. 170 of the 219 raw digests are ≥ p, so the reduction matters (**[verified]**).
- c₁ = 7120861356467848435263064379192047478074060781135320967663101236819528304084 and c₂₁₈ = 2119542016932434047340813757208803962484943912710204325088879681995922344971. These equal the circuit's `c_partial[0]` and `c_partial[217]` (218 entries, "doesn't contain the first and last round constants, which are always zero").
- c₀ = c₂₁₉ = 0.
- The npm 0.1.7 build used ethers' `keccak256(toUtf8Bytes(...))`. It gives the same values.

**Feistel permutation** `MiMCFeistel(nrounds=220)` with key k:
```
for i in 0..219:
  t = k + xL + c_i              (c_0 = 0; JS skips c for i == 0)
  if i < 219: (xL, xR) = (xR + t^5, xL)
  else:       xR = xR + t^5     (no swap in last round; xL unchanged)
```
This matches the paper's 2n/n Feistel with x⁵, + replacing ⊕, and **no final key addition**.

**Sponge** `MiMCSponge(nInputs, nRounds=220, nOutputs)` (circuit) / `multiHash(arr, key=0, numOutputs=1)` (JS):
```
R = 0; C = 0
for x in ins: R = R + x; (R, C) = Feistel_k(R, C)     // rate 1 (R, "xL"), capacity 1 (C, "xR")
outs[0] = R
repeat nOutputs-1 times: (R, C) = Feistel_k(R, C); output R
```
- There is no padding and no length encoding. The circuit's first stage takes xL = ins[0] and xR = 0, which is the same thing.
- JS `multiHash([])` returns 0. The circuit needs nInputs ≥ 1.

**KATs** (circomlibjs `test/mimcsponge.js`, k = 0, 1 output):
- `multiHash([1,2]) = 0x2bcea035a1251603f1ceaf73cd4ae89427c47075bb8e3a944039ff1e3d6d2a6f` = 19814528709687996974327303300007262407299502847885145507292406548098437687919
- `multiHash([1,2,3,4]) = 0x3e86bdc4eac70bd601473c53d8233b145fe8fd8bf6ef25f0b217a1da305665c` = 1767591491111054304950637348678561461191266274283762027709516319108521879132

Extra vectors I generated by running circomlibjs 0.1.7 (same code lineage as the above, so not independent):
- `hash(xL=1, xR=2, k=3) = (18444058245820418255538785847032978363886102372504864086197416499869253008979, 2646733164649743153031645792459389637917704265581895142760676293265176296759)`. This is the circomlib circuit-test permutation input.
- `hash(0,0,0) = (14543742788565021628577424853847564376151732847602780516906950225481254681152, 21165881269406212375659499083070944693027168220143204011932538650149052385959)`
- `multiHash([1,2], 0, 3) = [19814528709687996974327303300007262407299502847885145507292406548098437687919, 21479918933254162297266020499931408698629819071798560668427831994080392652265, 5864304407125602198417538232776668609689728417208547813776331040141674798262]`
- `multiHash([0]) = 14543742788565021628577424853847564376151732847602780516906950225481254681152`
- `multiHash([1], key=7) = 18457887129245626032172711944503166400228874031172347600648176248818778205341`

Other cross-validation sources:
- Kestrel ACL2 Semaphore MiMCSponge tests (BSD-3; LIT-REVIEW §5.2). These are independent.
- Tornado Cash / Semaphore Solidity `MiMCSponge` contracts generated by `mimcsponge_gencontract.js`. These are the same lineage.

### 3.3 circomlib MiMC7 (x⁷, 91 rounds): mention only
Sources: `circuits/mimc.circom` `MiMC7(nrounds)` and `src/mimc7.js`.
- Seed "mimc". Constants: c = keccak(seed), then iterated keccak as above, with **only c₀ = 0** (c₉₀ is nonzero).
- Round i: t = k + x_i + c_i (c₀ = 0), x_{i+1} = t⁷. Output t₉₀⁷ + k. This is MiMC-n/n with the final key addition.
- `multiHash(arr, key)` is Miyaguchi–Preneel-like: r ← r + x_i + MiMC7_r(x_i), with r₀ = key or 0.
- KATs:
  - `multiHash([1,2]) = 0x0b91ebbd35d7448ecc13e75a7ceb1ce5bbe428090acfae0da2c3867a874ce6ea` (= 5233261170300319370386085858846328736737478911451874673953613863492170606314)
  - `multiHash([1,2,3,4]) = 0x19ce9298d9e8ada63b2fb30c938d25cc9116aca2795f8b90fd9530687b4ad075`
  - From my run: `hash(1,2) = 10594780656576967754230020536574539122676596303354946869887184401991294982664`.
- It is cheap to add if MiMC-n/n is specified generically, and gives an "n/n" instance in actual use.

### 3.4 Rust oracles for MiMC
- **`arkworks-mimc` 0.3.0** (Tetration-Lab/arkworks-mimc @aad853f1, **LGPL-3.0-only**).
  - Implements `permute_feistel` (MiMC-2n/n sponge, circomlib-compatible) and `permute_non_feistel` (MiMC7-style).
  - `src/params/mimc_5_220_bn254.rs` gives round keys "0", 7120861…, …, which are the circomlibjs constants (README: "pre-generated round keys … available in circomlibjs").
  - The Feistel code matches circomlibjs, including no swap in the last round and skipping the constant at i = 0.
  - Its code is independent of circomlibjs but its constants are copied. Prefer computing constants ourselves (Keccak-256 is already in the repo) and treat the crate as a permutation and sponge oracle. Check LGPL compatibility for linking in the harness (dev-only use is probably fine).
- `mimc-rs` 0.0.2 (GPL-3.0, 2019, MiMC7 only), `near_mimc`, `stealth-lib`: low-value or unvetted.
- `light-hasher` (Light Protocol) is Poseidon/Keccak/SHA, not MiMC as far as I saw (not deeply checked).

---

## 4. Pedersen hash on BabyJubJub (circomlib)

### 4.1 Curve: BabyJubJub (normative values from circomlibjs `src/babyjub.js`; EIP-2494, now "Moved"; iden3 `Baby-Jubjub.pdf` §4)
- Field: F_p with p = BN254 Fr (above).
- Twisted Edwards: A·x² + y² = 1 + D·x²y² with **A = 168700, D = 168696**. A is a square and D a non-square (**[verified]**), so the addition law is complete.
- Addition (`addPoint`): x₃ = (x₁y₂ + y₁x₂)/(1 + D x₁x₂y₁y₂) and y₃ = (y₁y₂ − A x₁x₂)/(1 − D x₁x₂y₁y₂). The identity is (0, 1).
- order = 21888242871839275222246405745257275088614511777268538073601725287587578984328 = 8·subOrder, with subOrder (prime) l = 2736030358979909402780800718157159386076813972158567259200215660948447373041.
- `Generator` = (995203441582195749578291179787384436505546430278305826713579947235728471134, 5472060717959818805561601436314318772137091100104008585924551046643952123905).
- `Base8` = 8·Generator = (5299619240641551281634865583518297030282874472190772894086521144482721001553, 16950150798460657717958625567821834550301663161624707787222815936182638968203) (**[verified]**). Base8 is not used by the Pedersen hash.
- Montgomery form (`circuits/montgomery.circom`, iden3 doc §4.1):
  - Curve: B v² = u³ + A_M u² + u with A_M = 2(A+D)/(A−D) = 168698 and B_M = 4/(A−D) = 1, i.e. **v² = u³ + 168698u² + u**.
  - Maps: (x, y) ↦ (u, v) = ((1+y)/(1−y), (1+y)/((1−y)x)) and back (u, v) ↦ (u/v, (u−1)/(u+1)).
  - The circuit computes inside a segment in Montgomery form, then converts back.
- The iden3 Pedersen doc §4.1 writes the Edwards curve as x² + y² = 1 + d'x²y² with d' = 9706598848417545097372247223557719406784115219466060233080913168975159366771 (the A = 1 isomorphic form). The implementation uses A = 168700, D = 168696. **Use the implementation's form.**
- **Point packing** (`packPoint`/`unpackPoint`):
  - 32 bytes: y little-endian, with bit 255 (0x80 of byte 31) set iff x > (p−1)/2.
  - Unpack:
    - Read the bit and clear it.
    - Reject if y > p. Note the quirk: y = p is not rejected.
    - Compute x² = (1−y²)/(A − D y²) and reject if the Euler criterion ≠ 1. This also rejects x² = 0, i.e. y = ±1.
    - Take x = F.sqrt(x²) and negate it if the bit is set.
  - Empirically the wasm `F.sqrt` (ffjavascript 0.2.63) returns the root ≤ (p−1)/2 (38/38 samples), so unpack is the inverse of pack for x ≠ 0. This is a load-bearing convention for generator derivation. For the spec, prove the ten bases equal the hard-coded values rather than modelling ffjavascript.

### 4.2 Pedersen hash algorithm (normative: circomlibjs `src/pedersen_hash.js` + circomlib `circuits/pedersen.circom`)
Constants: `windowSize = 4`, `nWindowsPerSegment = 50`, so 200 bits per segment.
- Message: bytes to bits, **LSB-first per byte** (`buffer2bits`: bit 8i + j = (byte_i >> j) & 1).
- nSegments = ⌊(nbits − 1)/200⌋ + 1. For nbits = 0 that is 0 segments, and the hash is the packed identity `01 00…00`.
- For segment s, the bits are bits[200s .. 200s+200). The last segment may be shorter, with nWindows = ⌊(segbits − 1)/4⌋ + 1.
- Each window w has bits b0 b1 b2 b3. Missing trailing bits count as 0; JS does this by bounds checks, the circuit by zero padding.

  enc = (1 + b0 + 2·b1 + 4·b2) · (b3 ? −1 : +1)

  **Sign convention: b3 = 1 means negative.** The iden3 doc §4.2 writes enc = (2b3 − 1)(…), i.e. the opposite sign. **The doc disagrees with the code; the code is normative.**
- Segment scalar e_s = Σ_w enc_w · 32^w (`exp` shifts by windowSize + 1 = 5 bits). If e_s < 0, add subOrder. The bases are in the order-l subgroup, so this is just e_s mod l.
- H(M) = Σ_s e_s · P_s on twisted Edwards, and the output is **packPoint(H)**: 32 bytes.
  - The circuit `Pedersen(n)` outputs the unpacked (x, y) instead. It supports at most 10 segments (2000 bits), with BASE[10] hard-coded.
  - circomlib `pedersen_old.circom` is a different, older construction (250-bit chunks, `EscalarMul`). It is not the same hash.

**Generators** (`getBasePoint("blake", i)`):
```
for tryIdx = 0,1,...:
  S = "PedersenGenerator" + "_" + leftpad0(i,32) + "_" + leftpad0(tryIdx,32)   // ASCII, decimal, zero-padded to 32 chars
  h = BLAKE-256(S)            // BLAKE (SHA-3 finalist, 14 rounds) 256-bit, NOT BLAKE2; npm "blake-hash"/@noble blake1
  h[31] &= 0xBF               // clear bit 254
  p = unpackPoint(h)          // bit 255 = sign
  if p != null: break
P_i = 8 · p                   // cofactor clearing; must be in subgroup
```
**[verified]**: I reran this with circomlibjs 0.1.7 and it reproduces all ten circuit BASE points. Empty-string BLAKE-256 = 716f6e863f744b9ac22c97ec7b76ea5f5908bc5b2f67c61510bfc4751384ea7a, the official BLAKE-256 vector, which confirms the 14-round final BLAKE. Successful tryIdx per base:
- 0, 2, 4, 5, 6 and 8: tryIdx 0
- 1 and 7: tryIdx 2
- 9: tryIdx 1

BASE[0] = (10457101036533406547632367118273992217979173478358440826365724437999023779287, 19824078218392094440610104313265183977899662750282163392862422243483260492317). All ten are in `pedersen.circom` lines `var BASE[10][2]`.

The iden3 doc §5.1 says the generators come from Keccak256(D‖S) with a byte S. **That is wrong relative to the code.**

**Hash dependency.** Generator derivation needs **BLAKE-256 (BLAKE1)**, which the repo does not have (it has BLAKE2 and BLAKE3). Options:
- (a) Add a small BLAKE-256 reference: 14 rounds, ChaCha-like G with the constant table, 512-bit blocks, and its own padding with 0x01 marker bits and a counter. Then prove the derivation.
- (b) Take the 10 bases as constants with documented provenance (circuit file), and verify on-curve, in-subgroup (l·P = 0) and the BLAKE-256 derivation only in Layer 3.

(a) matches the "constants are theorems" policy.

**KATs**
- circomlibjs `test/pedersenhash.js`: `hash("Hello")` = `0e90d7d613ab8b5ea7f4f8bc537db6bb0fa2e5e97bbac1c1f609ef9e6a35fd8b` (packed). Unpacked: x = 13057869703420394250544403835227057665059779354002305870213426705081885688482 and y = 5422822308853265117631996831487612352180561624992420021537578261723609534478.
- circomlib `test/pedersen2.js` compares the circuit `Pedersen(256)` against JS for the input 0 (32 zero bytes) and for 253 ones (bytes FF×31, 0x1F). My computed packed outputs:
  - zero32 → `37cfc3c92b8721bd82a7aa437c97cb4d7ef88399d666f72cae0d73558f867a2d`
  - 253 ones → `196ebde0dee38766b88eeb43fc4effef94209858eef1bc0913a6d3dab27171ab`
- Other self-generated (circomlibjs 0.1.7):
  - `hash("abc")` = `7f9fdf1e8fbd4dbbacb1c28341caf3a95e50a523aeb51281c2fbcd517488708a`
  - `hash([0x01])` = `75c28cc0b8c45fa951bd48ffeb096e3373dac173ee78fc7b58e9ce8dc193b01d`
  - `hash(0xAB×64)` = `52d778c60b7c871f933af3544fdf65781a1adb88eaa946c1a8567c55bd6afa0e` (3 segments)
  - `hash("")` = `0100…00`

**Rust oracles for BabyJubJub and Pedersen**
- `babyjubjub-rs` 0.0.11 (arnaucube, Apache-2.0, @367ee99d): curve, EdDSA and Poseidon. **No Pedersen hash.** It uses blake-hash Blake512 for EdDSA keys. It is useful only as a curve oracle (it uses the same A and D as circomlib).
- `ark-ed-on-bn254` 0.6.0 (arkworks, MIT/Apache) is BabyJubJub, but I believe in the A = 1 isomorphic form with d' as in the iden3 doc and a different generator (**unverified**). Points would need the isomorphism x ↦ x·√A.
- `taceo-ark-babyjubjub` 0.6.0 (MIT/Apache) claims circom compatibility. Not inspected.
- `webb-pedersen-hash` 0.1.0 (GPL-3.0, 2021) is possibly circom-compatible. Not inspected.
- **No well-established independent Rust circomlib-Pedersen oracle was found.** Practical options:
  - Call circomlibjs (GPL-3.0, node) from the harness.
  - Write a ~50-line Rust oracle on babyjubjub-rs plus a `blake-hash` BLAKE-256 crate.
  - Vendor KATs only.

---

## 5. Noir Pedersen hash and commitment on Grumpkin

### 5.1 Definition (noir_stdlib `src/hash/mod.nr` @5662e904, lines 48–111)
```noir
pub fn pedersen_commitment_with_separator<let N: u32>(input: [Field; N], separator: u32) -> EmbeddedCurvePoint {
    points[i] = EmbeddedCurveScalar::from_field(input[i]);           // lo/hi 128-bit limbs
    let generators = derive_generators("DEFAULT_DOMAIN_SEPARATOR".as_bytes(), separator);  // indices separator..separator+N-1
    multi_scalar_mul(generators, points)
}
pub fn pedersen_hash_with_separator<let N: u32>(input: [Field; N], separator: u32) -> Field {
    // scalars[i] = from_field(input[i]); generators[i] = derive_generators("DEFAULT_DOMAIN_SEPARATOR", separator)[i]
    scalars[N] = EmbeddedCurveScalar { lo: N as Field, hi: 0 };
    generators[N] = derive_generators("pedersen_hash_length".as_bytes(), 0)[0];
    multi_scalar_mul_array_return(generators, scalars, true)[0].x
}
pedersen_hash(x) = pedersen_hash_with_separator(x, 0); pedersen_commitment(x) = ..._with_separator(x, 0)
```
Mathematically:
- **commit_sep(x) = Σᵢ xᵢ·G_{sep+i}**
- **hash_sep(x) = (Σᵢ xᵢ·G_{sep+i} + N·H).x**

where:
- G_j = derive_generators("DEFAULT_DOMAIN_SEPARATOR")[j]
- H = derive_generators("pedersen_hash_length")[0]
- xᵢ ∈ BN254 Fr is taken as an integer (< r) and used as a Grumpkin scalar. The Grumpkin scalar field is BN254 Fq, which is greater than r, so the embedding is injective.

The point at infinity encodes as (0, 0, is_infinite = true), so its .x is 0. Barretenberg's native `pedersen_hash::hash` **throws on empty input**; Noir with N = 0 gives (0·H).x, i.e. infinity, i.e. 0 (edge case, unverified at runtime). The separator is the *starting generator index*, not a domain string.

**Grumpkin**: y² = x³ − 17 over F_q with q = BN254 Fr = 21888242871839275222246405745257275088548364400416034343698204186575808495617. Group order = BN254 base-field prime 21888242871839275222246405745257275088696311157297823662689037894645226208583 (prime, cofactor 1).

### 5.2 Generator derivation
Sources: barretenberg `ecc/groups/group.hpp::derive_generators`, `affine_element_impl.hpp::hash_to_curve` and `derive_from_x_coordinate`, and Noir's Rust port in `acvm-repo/bn254_blackbox_solver/src/generator/{generators.rs, hash_to_curve.rs}`. The hash is **BLAKE3** (`blake3s_constexpr`), not blake2s or keccak.
```
derive_generators(domain_bytes, num, start):
  preimage[0..32)  = BLAKE3(domain_bytes)          // plain hash mode, 32-byte output
  preimage[32..64) = 0
  for i in start .. start+num:
    preimage[32..36) = BE32(i)
    G_i = hash_to_curve(preimage, attempt=0)

hash_to_curve(seed, a):                            // seed is 64 bytes here
  buf = seed ‖ [a, 0];  hi = BLAKE3(buf)            // 66-byte input
  buf = seed ‖ [a, 1];  lo = BLAKE3(buf)
  x = (int_be(hi) · 2^256 + int_be(lo)) mod q
  yy = x^3 − 17
  if yy is a non-residue: return hash_to_curve(seed, a+1)
  y = sqrt(yy);  sign = (hi[0] > 127)               // top bit of first byte of hi
  if (y mod 2) != sign: y = −y                      // parity of canonical y equals sign bit
  return (x, y)
```
Barretenberg's code compares `uint256_t(y).get_bit(0)` (the LSB of y in canonical form) against the sign bit. The Rust doc comment wrongly says "most significant bit of y" and also says "for BN254, a = 0, b = 3". **The code uses the LSB and b = −17.** Lampe's `liftWithParity` agrees with the code.

**[verified]**: an independent Python implementation (hand-written single-chunk BLAKE3, checked against the BLAKE3 empty-string vector, plus Tonelli–Shanks and affine Weierstrass arithmetic) reproduces every listed KAT:
- hash_to_curve smoke test ([] → x = 24c4cb9c…c12e, y = 0668b8d6…0b2e)
- length generator H = (0x2df8b940e5890e4e1377e05373fae69a1d754f6935e6a780b666947431f2cdcd, 0x2ecd88d15967bc53b885912e0d16866154acb6aac2d3f85e27ca7eefb2c19083)
- default generator G₀ = (0x083e7911d835097629f0067531fc15cafd79a89beecb39903f69572c636f4a5a, 0x1a7f5efaad7f315c25a918f30cc8d7333fccab7ad7c90f14de81bcc528f9935d)
- the Noir and barretenberg hash vectors below

**KATs** (provenance in brackets; all **[verified]** by my Python):
- Noir stdlib `#[test] assert_pedersen` (hash/mod.nr ~L612–760), N = 1..10 with separator = N:
  - `pedersen_hash_with_separator([1],1) = 0x1b3f4b1a83092a13d8d1a59f7acb62aba15e7002f4440f2275edb99ebbc2305f`
  - `pedersen_commitment_with_separator([1],1) = (0x054aa86a…bde402, 0x209dcfbf…cac126)`, which equals G₁
  - `…hash([1,2],2) = 0x26691c129448e9ace0c66d11f0a16d9014a9e8498ee78f4d69f0083168188255`
  - `commit([1,2],2) = (0x2e2b3b19…7b0753, 0x2ff44824…4f8778)`
  - `…hash([1,2,3],3) = 0x0bc694b7…06dbe4`
  - `…hash([1,2,3,4],4) = 0x00dae10fb32a8408521803905981a2b300d6a35e40e798743e9322b223a5eddc`
  - and so on up to N = 10
- Noir `test_programs/execution_success/pedersen_hash` and `pedersen_check`: `pedersen_hash([0,1]) = 0x0d98561fb02ca04d00801dfdc118b2a24cea0351963587712a28d368041370e1`. Also `pedersen_commitment([0,1]) = G₁` (since 0·G₀ + 1·G₁).
- barretenberg `crypto/pedersen_hash/pedersen.test.cpp`:
  - `hash({1,1}) = 0x07ebfbf4df29888c6cd6dca13d4bb9d1a923013ddbbcbdc3378ab8845463297b`
  - `hash({1,1}, offset 5) = 0x1c446df60816b897cda124524e6b03f36df0cec333fad87617aab70d7861daa6`
  - length-generator test
- bn254_blackbox_solver `generators.rs` tests: all 8 default generators G₀..G₇ (x and y hex) plus the length generator. `hash_to_curve.rs` has 4 smoke vectors.
- Self-generated, my Python only (unconfirmed by Noir):
  - `pedersen_hash([1]) = 0x03542cb720369f19a74fd05b4edfbedb27a78514ad3283f1b3270a1656cced8e`
  - `pedersen_hash([1,2]) = 0x17cb544f4d22abbae88f69c706f21367d7925abb131a13836745714dc896c150`
  - `pedersen_hash([0]) = H.x`
  - `pedersen_hash([r−1]) = 0x08377d58…ca35`

Barretenberg also has `hash_buffer`: 31-byte big-endian chunks, chained pairwise. Noir does not expose it. Out of scope.

**Rust oracles**
- `bn254_blackbox_solver` 0.46.0 (crates.io; noir-lang/noir `acvm-repo/bn254_blackbox_solver`, MIT OR Apache-2.0). It exposes `derive_generators` and an MSM via `embedded_curve_ops`, and uses `ark-grumpkin` and `acvm_blackbox_solver::blake3` (the `blake3` crate).
  - This is a Rust port of barretenberg, "adapted from barustenberg (MIT)", so it is **not independent of barretenberg's algorithm** but is independent code.
  - A Pedersen hash is assembled from `derive_generators` plus `multi_scalar_mul`. Note: crate versions 0.4x track Noir releases.
- `ark-grumpkin` 0.6.0 (arkworks, MIT/Apache) provides the curve only.
- `noir_grumpkin` 0.1.0 provides the curve (not inspected).
- barretenberg itself is C++ (`bb` binary). It is a separate implementation lineage from the Rust port and gives a good second oracle via its CLI or WASM.

### 5.3 Lampe's Lean spec (LIT-REVIEW §5.7)
File: `Lampe/Lampe/Crypto/Pedersen.lean` (reilabs/lampe @13c210ef, Apache-2.0, Lean v4.29.1 + Mathlib v4.29.1). Supporting files: `Lampe/Lampe/Crypto/EmbeddedCurve.lean`, `Lampe/Lampe/Crypto/Blake3.lean` (a computable BLAKE3 including the tree), `Lampe/Lampe/Crypto/Bn254/Sqrt.lean` (Tonelli–Shanks), `stdlib/lampe/Stdlib/Hash/Pedersen.lean` (760 lines of Noir-extraction proofs), and `Lampe/Tests/Pedersen.lean`.

- Curve: `def curve (p) : WeierstrassCurve (Fp p) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := -17 }` and `abbrev affineCurve p := (curve p).toAffine`. This is **Mathlib's** `WeierstrassCurve.Affine.Point` group.
- `pedersenGenerator domain index : (affineCurve p).Point` follows the derivation above:
  - It uses `makePreimage` and `hashToCurve`, which is bounded at 256 attempts and returns 0 on exhaustion.
  - `liftWithParity` picks y with `y.val % 2 == signBit`, then checks the point with `curvePoint?`.
  - `pedersenGeneratorPoint p domain index` returns `pointAtInfinity` unless `p.natVal = r_scalar`.
- Main definitions (quoted):
```lean
def pedersenCommitment (p) [Bn254.Prime p] (domain) {n} (inputs : List.Vector (Fp p) n) (separator : Nat) : Point p :=
  encodeCurvePoint (∑ i : Fin n, Scalar.valueNat (Scalar.canonicalDecomp (inputs.get i)) •
                      pedersenGenerator (p := p) domain (separator + i.val))
def pedersenHash (p) [Bn254.Prime p] (domain) {n} (inputs : List.Vector (Fp p) n) (separator : Nat) : Fp p :=
  pointX (encodeCurvePoint ((∑ i : Fin n, Scalar.valueNat (Scalar.canonicalDecomp (inputs.get i)) •
                               pedersenGenerator (p := p) domain (separator + i.val))
                            + n • pedersenGenerator (p := p) pedersenHashLengthBytes 0))
```
  - `defaultDomainBytes` = ASCII "DEFAULT_DOMAIN_SEPARATOR".
  - `pedersenHashLengthBytes` = "pedersen_hash_length".
- Main theorems: `pedersen_hash_with_separator_spec_canonical`, `pedersen_commitment_spec_canonical` and `pedersen_hash_spec_canonical` (stdlib/lampe/Stdlib/Hash/Pedersen.lean ~L695–760). They prove the extracted Noir stdlib equals these closed forms.
- KATs in `Lampe/Tests/Pedersen.lean` use **`native_decide`**, which the repo bans in Layer 1. Expect `decide +kernel` to be slow but perhaps feasible: about 2 BLAKE3 calls per attempt, Tonelli–Shanks over a 254-bit field, and 254-bit scalar multiplications. This needs measuring; Nat arithmetic is GMP-accelerated in the kernel.
- Reuse potential: very close to what we would write. Our repo already has BLAKE3 (`Hash/BLAKE3`), so the generator derivation can be stated with our BLAKE3 and possibly bridged to Lampe later. Lampe pins an older Mathlib (v4.29.1) than ours (v4.34.0-era), so it cannot be a direct dependency, and its spec is tied to Lampe's `Tp`/`Fp p` types.

---

## 6. Mathlib support (local `.lake/packages/mathlib` @5ed2965256430c3649e86755f9576b54eca72435)

- **Short Weierstrass and affine group law are present.** Module `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` (plus `Affine/Basic.lean`, `Affine/Formula.lean`, `Affine/AddSubMap.lean`). There are also `Jacobian/{Basic,Formula,Point}.lean` and `Projective/{Basic,Formula,Point}.lean`, plus `Weierstrass.lean`, `VariableChange.lean`, `NormalForms.lean`, `ModelsWithJ.lean` and `DivisionPolynomial/`.
  - `structure WeierstrassCurve (R) where a₁ a₂ a₃ a₄ a₆ : R` (Weierstrass.lean:77).
  - `abbrev WeierstrassCurve.Affine R := WeierstrassCurve R` and `abbrev WeierstrassCurve.toAffine` (Affine/Basic.lean:74, 78).
  - `inductive WeierstrassCurve.Affine.Point | zero | some (x y : R) (h : W'.Nonsingular x y)`, `deriving DecidableEq` (Affine/Point.lean:478). A point carries a nonsingularity proof.
  - `instance : Zero W'.Point`, `def neg`, `instance : Neg`, `InvolutiveNeg`.
  - `def add : W.Point → W.Point → W.Point`. It requires `[Field F] [DecidableEq F]` and uses `slope`, `addX` and `addY` from Formula.lean (L175, L245, L262). `instance : Add W.Point`, `lemma add_def`.
  - Lemmas `add_some`, `add_of_Y_eq`, `add_self_of_Y_ne`, `add_of_X_ne`, `neg_some`, ….
  - `instance : AddCommGroup W.Point where nsmul := nsmulBinRec; zsmul := zsmulRec nsmulBinRec` (Point.lean:807). Associativity is proved via the class group of the coordinate ring (`toClass_injective`).
  - Scalar multiplication is therefore the generic `n • P` / `z • P` with **binary** recursion. `add`, `neg`, `slope`, `nsmulBinRec` are plain `def`s (not `noncomputable`), so they evaluate. Only the coordinate-ring machinery is noncomputable.
  - Grumpkin = `{a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := -17}` over `ZMod q`, which is exactly Lampe's approach.
- **No twisted Edwards curves in Mathlib.** `grep -ri edwards Mathlib` hits only an unrelated CStarAlgebra file, and there is nothing for Montgomery curves either. CompPoly in `.lake/packages` has no curve code.
  - **Workaround for BabyJubJub**: its Montgomery form v² = u³ + 168698u² + u is a Weierstrass curve with a₂ = 168698 and a₄ = 1 (B = 1, so no scaling is needed). So `WeierstrassCurve.Affine.Point` with `{a₁ := 0, a₂ := 168698, a₃ := 0, a₄ := 1, a₆ := 0}` over ZMod p gives the group for free, and circomlib's circuit computes in this form anyway.
  - The Edwards ↔ Montgomery birational map (u = (1+y)/(1−y), v = u/x; inverse x = u/v, y = (u−1)/(u+1)) must then be defined. Its exceptional points:
    - Edwards (0, 1) ↦ Montgomery O
    - (0, −1) ↦ (0, 0), the 2-torsion point
    - D non-square means no points at infinity on the Edwards side
  - It should be proved a group isomorphism, or at least used only as a codec for inputs and outputs.
  - Alternatively, define the Edwards group law directly and prove the group axioms. That is more work: associativity of the complete Edwards law is a known heavy proof, and no Mathlib infrastructure supports it.
- Prior art: Lampe (above) already uses Mathlib's affine Weierstrass group for Grumpkin, including `encodeCurvePoint` and `curvePoint?` codecs between (x, y, isInfinite) triples and `Affine.Point`.

---

## 7. Cross-cutting recommendations and risks
1. **Pin versions and record layouts.** Several of these change silently between versions:
   - Miden RPO layout changed at 0.21, empty `hash(bytes)` changed after 0.29, and empty-in-domain handling was added.
   - circomlib Pedersen has an "old" variant.
   - The iden3 Pedersen spec PDF disagrees with the code on the sign bit and on generator derivation (Keccak versus BLAKE-256).
   - The Noir Rust doc comments are wrong about the MSB and b = 3.
2. **Hash dependencies for "constants are theorems":**
   - SHAKE256 for Rescue-Prime and RPO is in the repo.
   - Keccak-256 for MiMC is in the repo.
   - BLAKE3 for Noir Pedersen is in the repo.
   - **BLAKE-256 (BLAKE1)** for circomlib Pedersen is **not** in the repo and would need adding.
3. **Abstract-group-first** (ROADMAP decision 6) fits well. Both Pedersen variants are "Σ scalar_i · G_i (+ N·H), then encode": BabyJubJub uses packed Edwards bytes and Noir uses Weierstrass x. The windowed signed-digit encoding (circomlib) and the lo/hi limb split (Noir) are scalar-side encodings over an abstract `AddCommGroup`.
4. **Licences for vendoring KATs.**
   - circomlib and circomlibjs are (L)GPL. Small numeric vectors are facts, but cite and check them.
   - Noir, barretenberg, miden-crypto, Marvellous, stark-anatomy and rpo are permissive.
   - arkworks-mimc is LGPL-3.0-only.
5. **Uncertainties.**
   - Winterfell Rp64_256 constant provenance is unknown.
   - matter-labs rescue_poseidon conformance to Algorithms 4 and 5 is unconfirmed.
   - The ark-ed-on-bn254 parameterisation is unverified.
   - Noir behaviour for N = 0 is unverified.
   - ffjavascript sqrt root choice is empirical (38/38). It is irrelevant if the bases are proved against the hard-coded values.
