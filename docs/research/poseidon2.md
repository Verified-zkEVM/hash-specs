> **Provenance.** Research notes compiled on 2026-10-12 by Claude Code research agents (see `AI_USE.md`) for Phases 4–5, from the pinned primary sources listed below. Paths such as `scratchpad/scripts/…` and `scratchpad/dl/…` refer to the agents' working files (Python checks and cloned sources), which are not vendored. Where these notes and the Lean specifications disagree, the Lean docstrings, which cite the primary sources, are authoritative.

# Poseidon2 research notes for hash-specs Phase 4

Compiled 2026-10-12. All sources pinned. No repo files were edited.

## Pinned sources

| Source | Repo / URL | Commit / version | Licence |
|---|---|---|---|
| Paper | ePrint 2023/323, obtained via `web.archive.org/web/2024id_/https://eprint.iacr.org/2023/323.pdf` (eprint.iacr.org returns 403 to scripts) | PDF CreationDate 2024-02-08; sha256 `6a59dd3f84cf918e08506e4320b29aec73eabe74cd3e3162f01ac53d6761e368` | n/a |
| HorizenLabs reference (crate `zkhash`) | HorizenLabs/poseidon2 | `055bde3f4782731ba5f5ce5888a440a94327eaf3` (2024-11-25, HEAD) | LICENSE-APACHE + LICENSE-MIT (crates.io says "MIT OR Apache-2.0"; GitHub reports Apache-2.0) |
| Plonky3 | Plonky3/Plonky3 | `90e266609b2dae40509442e0555936778def69d5` (2026-10-11, HEAD); workspace version 0.8.0; crates.io max 0.9.0-rc.1 | MIT OR Apache-2.0 |
| leanSpec | leanEthereum/leanSpec | HEAD `0b7d33ecbc9ee2435759c92de4da4d08d7faf1c8`; last commit with Poseidon2 `dbc2e778913d0a5a208f76f3bac0e0a7c401f976` | MIT |
| ArkLib | Verified-zkEVM/ArkLib | `db7005f84a9dbad7ff2abbbb4e8feeeac6f4dfd8` | Apache-2.0 |
| clean | Verified-zkEVM/clean | `b449bf590f93e13827c3c7e747e392d6969aa380` | MIT |
| risc0 | risc0/risc0 | `3bbcd44d6459b9ef6ac0df3846dc9215514934e8` | Apache-2.0 OR MIT |
| SP1 | succinctlabs/sp1 | `bfc27de3931d90bceb32eb42b922b0165f7f7bf0` | MIT OR Apache-2.0 |
| gnark-crypto | Consensys/gnark-crypto | `8911ee45d22bdf9d1c6ab4affe2d4f7ffaedd557` | Apache-2.0 |

Local copies of every fetched file are under `scratchpad/src/{hl,p3,ls,ark,other}`. The paper text is at `scratchpad/paper/p2.txt`. A small independent Python reference is at `scratchpad/scripts/p2.py`, with drivers `run1.py` to `run6.py`. It reproduces every KAT quoted below, which cross-checks the parameters recorded here.

---

## 1. Paper (Grassi, Khovratovich, Schofnegger; ePrint 2023/323, revision of 2024-02-08)

Caveat: section numbers are from this ePrint revision. The AFRICACRYPT 2023 LNCS version (pp. 177–203, doi 10.1007/978-3-031-37679-5_8) was not checked and may number them differently.

Table of contents (relevant parts): 3.2 "The Poseidonπ Permutation"; 4 "Security: Initial and Final Matrix Multiplications"; 5 "More Efficient Linear Layers"; 5.1 "Matrix for the External Round"; 5.2 "Matrix for the Internal Round"; 5.3 "Preventing Arbitrarily Long Subspace Trails"; **6 "Poseidon2π Specification"**; 7 Security Analysis (7.1 Statistical, 7.2 Algebraic, 7.3 Bariant et al.); App. A "Efficient Circulant MDS Matrices"; **App. B "Efficient Computation of M_E"**.

- **Permutation (Sec. 6):** `P2(x) = E_{RF-1} ∘ … ∘ E_{RF/2} ∘ I_{RP-1} ∘ … ∘ I_0 ∘ E_{RF/2-1} ∘ … ∘ E_0 (M_E · x)`. The initial `M_E · x` is the first difference from Poseidon. Sec. 4 justifies it: a sponge permutation must start and end with a linear layer.
- **External round (Sec. 6):** `E_i(x) = M_E · ((x_0+c_0^(i))^d, …, (x_{t-1}+c_{t-1}^(i))^d)`. Here d ≥ 3 is the smallest integer with gcd(d, p−1) = 1.
- **Internal round (Sec. 6):** `I_i(x) = M_I · ((x_0+ĉ_0^(i))^d, x_1, …, x_{t-1})`. It uses a single constant (Remark 4).
- **Domain:** p > 2^30 and t ∈ {2, 3, 4, …, 4t′, …, 24}.
- **M_E (Sec. 5.1):** for t = 4t′, `M_E = M4` if t = 4, and `circ(2·M4, M4, …, M4)` if t ≥ 8. M4 is defined as:
  ```
  M4 = [[5,7,1,3],[4,6,1,1],[1,3,5,7],[1,1,4,6]]
  ```
  This is M_{4,4}^{8,4} from [23] with α = 2. It is MDS for all p > 2^31. App. B gives the addition chain `t0=x0+x1; t1=x2+x3; t2=2x1+t1; t3=2x3+t0; t4=4t1+t3; t5=4t0+t2; t6=t3+t5; t7=t2+t4; out=(t6,t5,t7,t4)`, then `y_i = x'_i + Σ_{j≡i mod 4} x'_j`, which is the same as adding the column sum.
- **M_I (Sec. 5.2):** `M_I` has diagonal µ_0..µ_{t−1} and 1 everywhere else, so M_I = J + diag(µ−1). The µ_i are random elements of F_p∖{0,1}, chosen so that M_I is invertible and has no arbitrarily long subspace trails (Sec. 5.3). Sec. 5.3 gives a sufficient condition: the minimal polynomials of M_I, M_I², … are irreducible of maximum degree. The paper suggests storing µ_i − 1, so that `y_i = (µ_i−1)x_i + Σx`.
- **t ∈ {2,3} (Sec. 6, "Case: t ∈ {2,3}"):** **the paper says "compute M_I as before … impose MDS … set M_E = M_I".** It gives the MDS conditions on the µ_i, and choosing µ_i ∈ {2, …, p/4} satisfies them. **The paper does not contain `circ(2,1)`, `circ(2,1,1)`, `[[2,1],[1,3]]` or `[[2,1,1],[1,2,1],[1,1,3]]`.** These come from the HorizenLabs reference code and its sage script (section 2), where M_E ≠ M_I. **This is a real divergence from the paper's text. Every implementation I checked follows HorizenLabs here, for example Plonky3's BN254 instance. The spec should follow HorizenLabs and record the divergence.**
- **Round numbers:**
  - The rounds are those of Poseidon. Eq. (1) in Sec. 3.2 gives R_F = 8 and `R_P ≥ 1.075·max{⌈min{κ,log2 p}/log2 d⌉ + log_d t − 5, R_GB}`.
  - Sec. 6 says to use "the instance generation script provided by the authors" (footnote 9: hadeshash `generate_params_poseidon.sage`).
  - Table 1 lists (n,t,d) → (R_F,R_P): (31,16,5)→(8,14); (31,24,5)→(8,22); (64,8,7)→(8,22); (64,12,7)→(8,22); (256,2,5)→(8,56); (256,3,5)→(8,56).
  - BabyBear (d=7) and KoalaBear (d=3) are not in Table 1. Their values come from the script: see section 3.
- **Constants:** Sec. 6 says only "All round constants are generated as in Poseidonπ". The paper never says "Grain". The Grain LFSR comes in through the Poseidon paper (ePrint 2019/458) and the reference scripts.

---

## 2. HorizenLabs reference (`HorizenLabs/poseidon2@055bde3f…`)

### Permutation

The permutation is in `plain_implementations/src/poseidon2/poseidon2.rs`, `fn permutation`. It runs:

1. `matmul_external`
2. R_F/2 × (add_rc on all lanes, sbox on all lanes, matmul_external)
3. R_P × (`state[0] += rc[r][0]`, sbox_p(state[0]), `matmul_internal`)
4. R_F/2 full rounds

The S-box supports d ∈ {3, 5, 7}. The params struct asserts d ∈ {3, 5, 7, 11}, but d = 11 would panic in `sbox_p`.

### `matmul_external`

| t | Operation |
|---|---|
| 2 | `circ(2,1)`, computed as `x_i += x0+x1` |
| 3 | `circ(2,1,1)`, computed as `x_i += x0+x1+x2` |
| 4 | M4 via `matmul_m4` (the App. B chain). I verified by hand that it gives the matrix [[5,7,1,3],[4,6,1,1],[1,3,5,7],[1,1,4,6]]. |
| 8, 12, 16, 20, 24 | M4 on each block, then `input[i] += Σ_j input[4j + i%4]`, which is circ(2M4, M4, …) |

### `matmul_internal`

| t | Matrix |
|---|---|
| 2 | `[[2,1],[1,3]]`, computed as `x0 += s; x1 = 2x1 + s` |
| 3 | `[[2,1,1],[1,2,1],[1,1,3]]`, computed as `x0 += s; x1 += s; x2 = 2x2 + s` |
| 4–24 | `x_i = x_i·diag_m_1[i] + Σx` |

### BN254 t=3 instance (`plain_implementations/src/poseidon2/poseidon2_instance_bn256.rs`)

- Created as `Poseidon2Params::new(3, 5, 8, 56, &MAT_DIAG3_M_1, &MAT_INTERNAL3, &RC3)`, so t=3, d=5, R_F=8, R_P=56.
- `MAT_DIAG3_M_1 = [1,1,2]`, so µ = (2,2,3).
- `RC3` has 64 rows of 3 elements. In the 56 partial rows, only `[0]` is non-zero; the rest are padded with zeros. The first row starts with `0x1d066a255517b7fd8bddd3a93f7804ef7f8fcde48bb4c37a59a09a1a97052816`.
- Field: `fields/bn256.rs`, p = 21888242871839275222246405745257275088548364400416034343698204186575808495617.

**BN254 KAT** (`poseidon2.rs`, `mod poseidon2_tests_bn256`, `fn kats`). Input is `[0,1,2]`. Output:
```
0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033
0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570
0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8
```
My Python reference reproduces it.

### Other KATs in `poseidon2.rs` (all with input `[0..t-1]`)

- Goldilocks t=12.
- **BabyBear t=24:** `0x2ed3e23d, 0x12921fb0, 0x0e659e79, 0x61d81dc9, 0x32bae33b, 0x62486ae3, 0x1e681b60, 0x24b91325, 0x2a2ef5b9, 0x50e8593e, 0x5bc818ec, 0x10691997, 0x35a14520, 0x2ba6a3c5, 0x279d47ec, 0x55014e81, 0x5953a67f, 0x2f403111, 0x6b8828ff, 0x1801301f, 0x2749207a, 0x3dc9cf21, 0x3c985ba2, 0x57a99864`.
- BLS12-381 t=2, 3, 4.
- Pallas t=3.
- Vesta t=3.

**There is no BabyBear t=16 KAT upstream.** My reference computes HL BabyBear-16 on [0..15] as `[896560466, 771677727, 128113032, 1378976435, 160019712, 1452738514, 682850273, 223500421, 501450187, 1804685789, 1671399593, 1788755219, 1736880027, 1352180784, 1928489698, 1128802977]`. This value is not confirmed by any upstream source; run zkhash before relying on it.

### BabyBear instances (`poseidon2_instance_babybear.rs`)

- `POSEIDON2_BABYBEAR_16_PARAMS = new(16, 7, 8, 13, …)`
- `POSEIDON2_BABYBEAR_24_PARAMS = new(24, 7, 8, 21, …)`
- `MAT_DIAG16_M_1` is Grain-random full-size field elements: `0x0a632d94, 0x6db657b7, 0x56fbdc9e, 0x052b3d8a, 0x33745201, 0x5c03108c, 0x0beba37b, 0x258c2e8b, 0x12029f39, 0x694909ce, 0x6d231724, 0x21c3b222, 0x3c0904a5, 0x01d6acda, 0x27705c83, 0x5231c802`.
- There are no BabyBear 16/24 KAT values for HL other than the t=24 one above. There is no KoalaBear instance in HL.

### Generation script (`poseidon2_rust_params.sage`, repo root)

The script is single-instance: you edit `p` and `t` at the top.

- **α:** the smallest α ≥ 3 coprime to p−1.
- **Round numbers:** `poseidon_calc_final_numbers_fixed(p,t,alpha,128,True)`. This is a brute-force search with the Poseidon inequalities plus the ePrint 2023/537 bound, then the margin R_F += 2 and R_P = ⌈1.075·R_P⌉.
- **Grain LFSR:**
  - The 80-bit init is `field(2b)=1 | sbox(4b)=0 | n(12b) | t(12b) | R_F(10b) | R_P(10b) | 1×30`.
  - Taps are [62, 51, 38, 23, 13, 0].
  - 160 warm-up clocks.
  - Output uses the self-shrinking rule.
  - Bits are taken MSB-first in n-bit chunks, with rejection sampling while ≥ p.
- **Constant order:** `R_F·t + R_P` constants, in order `[R_F/2 · t external] [R_P internal] [R_F/2 · t external]`. The output pads each internal constant with t−1 zeros.
- **Matrices:**
  - `generate_matrix_full`: t=2 → `circulant([2,1])`; t=3 → `circulant([2,1,1])`; t=4 → M4; t ≡ 0 mod 4 → blocks `2·M4` on the diagonal and `M4` elsewhere.
  - `generate_matrix_partial`: t=2 → `[[2,1],[1,3]]`; t=3 → `[[2,1,1],[1,2,1],[1,1,3]]`; otherwise `circulant([0,1,…,1]) + diag(grain values)`, resampling until `check_minpoly_condition` holds.
  - **The diagonal is drawn from the same Grain stream after the round constants.**
- The script also computes `poseidon2([0..t-1])` and prints it as the test vector.
- Licence: the repo is dual MIT/Apache, so the constants can be vendored. Generating them is still better (see the ROADMAP).

---

## 3. Plonky3 (`Plonky3/Plonky3@90e26660…`, crates 0.8.0)

### Generic code

**`poseidon2/src/lib.rs`, `permute_mut`:** `external_layer.permute_state_initial` (initial M_E, then R_F/2 rounds), then `internal_layer.permute_state`, then `permute_state_terminal`.
- `SUPPORTED_WIDTHS = [2,3,4,8,12,16,20,24,32]`. Width 32 goes beyond the paper's t ≤ 24.
- The constructor asserts D ≥ 3 and R_F ≥ 6. Its comments cite paper Sec. 6 and Sec. 7.1.

**`poseidon2/src/external.rs`:**
- `HLMDSMat4` is [[5,7,1,3],[4,6,1,1],[1,3,5,7],[1,1,4,6]]. It is the paper/HL M4, labelled "the matrix used by the Horizon Labs implementation".
- **`MDSMat4` is a different matrix, `circ(2,3,1,1)` = [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]** ("the fastest 4x4 MDS matrix").
- `mds_light_permutation(state, mat4)`: t=2 and t=3 use the same circ(2,1)/circ(2,1,1) as HL. For t ∈ {4,8,…,32} it applies mat4 per block and then adds the column sums.

**Which M4 each field uses:**
- **`monty-31/src/poseidon2.rs` (BabyBear and KoalaBear) uses `&MDSMat4`.**
- Goldilocks and Mersenne-31 also use MDSMat4.
- **BN254 (`bn254/src/poseidon2.rs`) uses `HLMDSMat4`.**
- `GenericPoseidon2LinearLayers::external_linear_layer` defaults to `MDSMat4`.
- **So Plonky3's 31-bit instances use a different M_E from the paper and from HorizenLabs.**

**`poseidon2/src/internal.rs`, `matmul_internal`:** `state[i] = state[i]*diag_m_1[i] + Σstate`, i.e. M_I = J + diag(V), so µ_i = V_i + 1.

**Monty-31 fast path (`monty-31/src/poseidon2.rs`):** `state[0] = part_sum − state[0]`, which is V_0 = −2. It then calls `internal_layer_mat_mul(state, full_sum)`.

### Internal diagonal V, at HEAD

These are true field values. The code uses `.halve()` and `.div_2exp_u64(k)` on field elements, so V_i are the actual entries of diag(V).

| Instance | V |
|---|---|
| BabyBear-16 (`baby-bear/src/poseidon2.rs`) | `[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/2^27, -1/2^8, -1/16, -1/2^27]` |
| BabyBear-24 | `[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/16, 1/2^7, 1/2^9, 1/2^27, -1/2^8, -1/4, -1/8, -1/16, -1/32, -1/64, -1/2^7, -1/2^27]` |
| KoalaBear-16 (`koala-bear/src/poseidon2.rs`) | `[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/8, 1/2^24, -1/2^8, -1/8, -1/16, -1/2^24]` |
| KoalaBear-24 | `[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/16, 1/32, 1/64, 1/2^24, -1/2^8, -1/8, -1/16, -1/32, -1/64, -1/2^7, -1/2^9, -1/2^24]` |

**These are hand-picked, not Grain-drawn.** The source says they are chosen for cheap SIMD multiplication. Validity is argued through the minimal-polynomial condition (sage snippet in `poseidon2/src/internal.rs`).

**Montgomery history:** this caveat applies only to old Plonky3 versions and old KATs. In 2024 versions, for example `32d573593a6121faea34290100b0620f870f26ad`, `baby-bear/src/poseidon2.rs` defined `POSEIDON2_INTERNAL_MATRIX_DIAG_16_BABYBEAR_MONTY = [p-2, 1, 2, 4, …, 2^13, 2^15]`, with the comment "operate such that (1 + D(v)) is the monty form of the matrix". So the effective matrix was 2^-32·(J + diag(v)). This is my reading of that comment, not something I verified. The current semantic V was introduced with `9b267c411c` (2024-11, "Poseidon2 implementation for AVX2 and AVX512 …").

### Parameters at HEAD

| Field | p | d | R_F | R_P (w16 / w24 / w32) |
|---|---|---|---|---|
| BabyBear | 0x78000001 | 7 | 8 | 13 / 21 / 30 |
| KoalaBear | 0x7f000001 | 3 | 8 | 20 / 23 / 31 |

Sources:
- `BABYBEAR_S_BOX_DEGREE = 7` and `KOALABEAR_S_BOX_DEGREE = 3` are confirmed in the crate sources.
- The R_P constants are `BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_{16,24,32}` and `KOALABEAR_POSEIDON2_PARTIAL_ROUNDS_{16,24,32}`.
- The same numbers appear in the `poseidon2_round_numbers_128` table in `poseidon2/src/round_numbers.rs`.
- The KoalaBear-16 doc comment has a muddled derivation that mentions "85", but the constant used is 20, "per the official round number script".

### Round constants at HEAD

- They are Grain-LFSR generated. Doc comment: "Generated by the Grain LFSR with parameters: field_type=1, alpha=7 (exp_flag=0), n=31, t=16, R_F=8, R_P=13 … `poseidon2/generate_constants.py --field babybear --width 16`".
- They are split into `*_RC_{t}_EXTERNAL_INITIAL [[F;t];4]`, `*_RC_{t}_INTERNAL [F;R_P]` and `*_RC_{t}_EXTERNAL_FINAL`.
- `poseidon2/generate_constants.py` is a pure-Python port of the HL sage logic. It uses the same Grain init and stream order: external_initial, then internal, then external_final.
- It has its own `generate_internal_matrix` (Grain diagonal), but the Rust BabyBear and KoalaBear crates do **not** use it; they use the hand-picked V.
- Sample values:
  - BabyBear-16 initial row 0 starts `0x69cbb6af, 0x46ad93f9, …`.
  - KoalaBear-16 initial row 0 starts `0x7ee56a48, 0x11367045, …`.
  - KoalaBear-16 internal starts `0x54dfeb5d, 0x7d40afd6, …`.

### Plonky3 history that matters

1. **BabyBear constants:**
   - Added in `b7eabae20a1587be3b6ee6584fafde79636a7d0e` (2025-02-13, "babybear: add default poseidon2 impl with rc"). They were copied from HL `poseidon2_instance_babybear.rs`, as the comment there says.
   - They are unchanged to HEAD. I compared them programmatically against the parent of `0056fa83`.
2. **KoalaBear constants changed:**
   - Added in `80803612ff` (2025-08-25), generated with the HL sage script.
   - In that version the stream was laid out as ei | ef | it (initial, then final, then internal) instead of HL's ei | it | ef. For example, the old `KOALABEAR_RC16_EXTERNAL_FINAL[0]` starts with 1423960925 = 0x54dfeb5d, which is the HL-order internal[0].
   - **Fixed in `0056fa836d7fba9cb3fc77f3bbc47abd59c80ac0` (2026-03-09, "poseidon1: fix round constants for KoalaBear and BabyBear (#1398)")**, which reordered them to ei | it | ef.
   - So "Plonky3 KoalaBear Poseidon2" names **two different permutations** depending on version. The fix shipped in a release after 0.5.x. Pin ≥ 0.6.0, or better, pin by commit.

### Known-answer tests at HEAD (`#[cfg(test)] mod tests`)

All results below were reproduced by my independent Python reference.

**`test_default_babybear_poseidon2_width_16`** (canonical, Grain constants)
- Input: `[894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913]`
- Output: `[516096821, 90309867, 1101817252, 1660784290, 360715097, 1789519026, 1788910906, 563338433, 319524748, 1741414159, 1650859320, 894311162, 1121347488, 1692793758, 1052633829, 1344246938]`

**`test_default_babybear_poseidon2_width_24`**
- Input: `[886409618, 1327899896, 1902407911, 591953491, 648428576, 1844789031, 1198336108, 355597330, 1799586834, 59617783, 790334801, 1968791836, 559272107, 31054313, 1042221543, 474748436, 135686258, 263665994, 1962340735, 1741539604, 2026927696, 449439011, 1131357108, 50869465]`
- Output: `[882297297, 1264077610, 512812497, 782602970, 867738552, 1251075457, 309180082, 340784773, 524041877, 351272188, 404451680, 15001466, 322926653, 1773004150, 1718440818, 674682955, 1154713225, 1719133502, 324232301, 1005243141, 443371079, 268735940, 770060019, 718377682]`
- This KAT was not reproduced by my reference; only the width-16 vectors were.

**`test_default_koalabear_poseidon2_width_16`** (same 16-element input as BabyBear above)
- Output: `[1934285469, 604889435, 133449501, 1026180808, 1830659359, 176667110, 1391183747, 351743874, 1238264085, 1292768839, 2023573270, 1201586780, 1360691759, 1230682461, 748270449, 651545025]`

**`test_default_koalabear_poseidon2_width_24`** (same 24-element input as BabyBear above)
- Output: `[382801106, 82839311, 1503190615, 1987418517, 854076995, 1862291425, 262755189, 1050814217, 722724562, 741265943, 1026879332, 754316749, 1966025564, 1518878196, 502200188, 1368172258, 845459257, 1711434837, 724453836, 171032289, 655223446, 1098636135, 407832555, 1707498914]`
- This KAT was not reproduced by my reference; only the width-16 vectors were.

**Width 32:** KATs for both fields are also in the files, under `test_default_*_width_32`.

**`test_poseidon2_width_16_random` and `test_poseidon2_width_24_random`: do not use as spec oracles.**
- These use **random constants**: `Xoroshiro128Plus::seed_from_u64(1)` + `Poseidon2*::new_from_rng_128`. The output depends on how the `rand` crate samples field elements, and the expected values are tied to the dependency versions (`rand_xoshiro = "0.8.1"`; deps bumped in `8715fb14ca`, 2026-02-09). The sage counterpart is referenced as `0xPolygonZero/hash-constants`.
- They are not a real instance. Values at HEAD:
  - BabyBear w16: `[1255099308, 941729227, 93609187, 112406640, 492658670, 1824768948, 812517469, 1055381989, 670973674, 1407235524, 891397172, 1003245378, 1381303998, 1564172645, 1399931635, 1005462965]`
  - KoalaBear w16: `[652590279, 1200629963, 1013089423, 1840372851, 19101828, 561050015, 1714865585, 994637181, 498949829, 729884572, 1957973925, 263012103, 535029297, 2121808603, 964663675, 1473622080]`
- Note: the BabyBear random-24 input array is **not** the same as the default-24 input. It lacks 2026927696 and ends in 1589724894.

**Pre-March-2026 KoalaBear default KAT** (parent of `0056fa83`, `4341702be337f95d1f8f7f7e9188199b98726d92`): w16 output `[190453639, 458899855, 383789123, 1958965770, 1470307143, 135446903, 1980271247, 26609194, 337889870, 543343594, 900082402, 1267415354, 1018710090, 902823573, 1161524658, 1483653556]`.

**Plonky3 BN254 (`bn254/src/poseidon2.rs`):**
- t=3, d=5, R_F=8, R_P=56, `HLMDSMat4` (unused at t=3, where circ(2,1,1) applies).
- Internal matrix: `[[2,1,1],[1,2,1],[1,1,3]]`.
- Test `test_poseidon2_bn254` checks against `zkhash` from `{ git = "https://github.com/HorizenLabs/poseidon2" }`, i.e. it is HL-compatible.

---

## 4. leanSpec, ArkLib, clean

### leanSpec

**leanSpec HEAD has no Poseidon2.**
- PR #496, commit `e545e14ec0a4a58bcdb7d37dfef08fa9afd614ab` (2026-04-06, "Update multisig bindings…", first bullet "cryptography: replace Poseidon2 by Poseidon1"), deleted `src/lean_spec/subspecs/poseidon2/{permutation,constants}.py`.
- HEAD has `src/lean_spec/spec/crypto/poseidon.py`. This is **Poseidon1 over KoalaBear**:
  - widths 16 and 24, d=3, R_F=8, R_P=20 (w16) and 23 (w24);
  - full (R_F+R_P)·t Grain constants;
  - a circulant MDS with first row `[1,1,51,1,11,17,2,1,101,63,15,2,67,22,13,3]`, from Plonky3 `koala-bear/src/mds.rs`;
  - no initial linear layer.
- HEAD KAT fixtures are under `tests/consensus/lstar/poseidon/test_permutation_width{16,24}.py`. They are out of scope for Poseidon2, but relevant if the project also does Poseidon1 instances.

**Last Poseidon2 version** (`dbc2e778913d0a5a208f76f3bac0e0a7c401f976`, `src/lean_spec/subspecs/poseidon2/permutation.py`):
- KoalaBear, widths 16 and 24, d=3, R_F=8, R_P=20 / 23.
- `_M4_T = [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]].T`, i.e. Plonky3's MDSMat4, **not** the paper's M4.
- Diagonal: the same V vectors as Plonky3, given as `Fp` fractions.
- Internal layer: `sum + diag*state`.
- Constants in `constants.py` are flat lists, `_RAW_CONSTANTS_16` with 148 = 64+20+64 entries.

**leanSpec constant history:**

| Commit | Date | Constant layout | w16 KAT starts |
|---|---|---|---|
| `7e867836127ede70dcdf9335f054fc5c10e256bd` ("update constants") | 2025-08-19 | HL order; equal to current Plonky3 | `1934285469, …` (matches Plonky3 HEAD) |
| `87e567777058d2e11626e8716e1db0ce5fc65880` ("Poseidon2: reorder constants as per Plonky3 (#251)") | 2026-01-03 | Copied Plonky3's then-incorrect ei/ef/it layout | `190453639, …` |

That later layout stayed until Poseidon2 was removed. Its final tests (`tests/lean_spec/subspecs/poseidon2/test_permutation.py@dbc2e778`) used:
- `EXPECTED_16 = [190453639, …]`, the same as pre-fix Plonky3 above;
- `EXPECTED_24 = [556605495, 885256863, 899046610, 1365261647, 799824470, 1363091631, 588658632, 173515151, 783308499, 1346358755, 1865380489, 1166148328, 1402826941, 434428806, 928050984, 1402941053, 201160368, 1850628943, 651578331, 12196116, 759351756, 948448587, 1529251366, 456048743]`.

My reference reproduces both.

**Conclusion:** "leanSpec KoalaBear Poseidon2" is ambiguous across its history. Pin by commit, or use the current Plonky3 instance.

### ArkLib (`ArkLib/Data/Hash/Poseidon2.lean@db7005f8…`)

- Says it was "translated from leanSpec … on Sep 12, 2025".
- `structure Params` has `width`, `numFullRounds`, `numPartialRounds`, `internalDiagVectors : Vector KoalaBear.Field width`, `roundConstants : Vector _ (numFullRounds*width + numPartialRounds)`, `width_dvd_by_4` and `numFullRounds_even`.
- `params16` is (16, 8, 20) and `params24` is (24, 8, 23). The diagonal vectors are the Plonky3 V, written as field fractions.
- `sBoxDegree := 3`.
- `m4Matrix = [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]`, i.e. Plonky3 MDSMat4.
- The external layer is the per-chunk M4 plus column sums; the internal layer is `sumAll + d*s`.
- It works over `CompPoly.Fields.KoalaBear` using `Vector` and `Fin.foldl`. There is no test and no `#eval` KAT.
- **Its constants (`rawConstants16`, `RAW_CONSTANTS_24`) are exactly leanSpec @ `7e867836` and exactly current Plonky3 (ei | it | ef).**

**Bug found in `permute`:**
- The full rounds take `rcs.extract rc_idx (rc_idx + params.width)`, so round r uses constants `[r, r+width)` instead of `[r·width, (r+1)·width)`.
- The bug is present in every version: `d35b6d06`, `e9b58305`, `42ff7f28` and HEAD.
- It affects both halves; the partial rounds and the `drop` arithmetic are correct.
- Result on the standard w16 input:
  - ArkLib `permute` gives `[1237797974, 1287852510, 2019029484, …]`;
  - with the indexing fixed it gives Plonky3 HEAD's `[1934285469, …]`.
- **ArkLib's Poseidon2 therefore matches no reference implementation.** This is worth reporting upstream, and it is a strong argument for the project's own spec plus KAT tests.

### clean

`Verified-zkEVM/clean@b449bf59` has **no Poseidon2**. It only has Poseidon: `Clean/Specs/Poseidon{,Optimized,Constants}.lean` and `Clean/Circomlib/Poseidon.lean`.

---

## 5. Rust and other oracle implementations

| Implementation | Instances | Independence |
|---|---|---|
| `p3-poseidon2`, `p3-baby-bear`, `p3-koala-bear` (crates.io 0.9.0-rc.1, 2026-10-11; repo at 0.8.0; MIT OR Apache-2.0) | BabyBear and KoalaBear w16/24/32; Goldilocks; M31; BN254 t=3 | Primary for 31-bit fields. Its BabyBear constants come from HL. |
| `zkhash` (crates.io 0.2.0, 2024-07-05, MIT OR Apache-2.0; the repo is the source of truth, and Plonky3 uses it as a git dependency) | `poseidon2` module: BabyBear t16/24, Goldilocks t8/12/16/20, BLS12-381 t2/3/4/8, BN256 t3, Pallas t3/4/8, Vesta t3. **No KoalaBear, no BN254 t=4.** | The original reference by the paper's author (Schofnegger). Its ark-ff dependency is old (0.4). |
| risc0 `risc0-zkp` (`risc0/zkp/src/core/hash/poseidon2/{mod,consts}.rs`) | BabyBear t=24, R_P=21, x^7; HL M4; `M_INT_DIAG_HZN` = HL `MAT_DIAG24_M_1`; HL constants (zero-padded) | An independent reimplementation ("thanks to nhukc") of the **HL BabyBear-24** instance. Its test `poseidon2_test_vectors` checks the HL [0..23] KAT `0x2ed3e23d…`. A good second oracle for HL BabyBear-24. |
| SP1 (`slop/crates/koala-bear/src/koala_bear_poseidon2.rs`, `crates/primitives`) | KoalaBear t=16, R_F=8, R_P=20, d=3. Constants in `RC16` start `0x7ee56a48`, as in Plonky3; it reorders them in `koala_bear_round_consts()`. | **Not independent.** It builds on a Plonky3 fork (`slop_poseidon2` re-exports `p3-poseidon2`, with the older `Poseidon2ExternalMatrixGeneral`/`DiffusionMatrixKoalaBear` API). I did not check whether its KAT equals current Plonky3. SP1's older `RC_16_30` table ("created by a RNG") is separate. |
| gnark-crypto (Go) | `field/babybear/poseidon2`, `field/koalabear/poseidon2`; BN254 and BLS curves under `ecc/*/fr/poseidon2` | The Go code is independent. The BabyBear package has `plonky3_interop_test.go`, with vectors from Plonky3 `de2b3b788660…` `default_babybear_poseidon2_16()`, so it is the same instance as Plonky3. **The curve instances derive constants from a Keccak-256 seed (`initRC`), not Grain, so they are a different instance from HL BN254.** I did not check which KoalaBear vintage the koalabear `test-vectors.json` matches. |
| crates.io `poseidon2` 0.0.1 (blueshift-gg, MIT, 2026-07) | BN254 t=3, "Horizen Labs parameters" | A new third-party crate; quality unknown. |
| `taceo-poseidon2` 0.3.1 (MIT/Apache) | BN254 | Not inspected. |
| Aztec/Noir barretenberg | BN254 t=4 | Not inspected here. It is the instance Lampe trusts, according to LIT-REVIEW. |

**Recommended oracles:**
- BabyBear and KoalaBear: Plonky3 `default_*` at a pinned commit after `0056fa83`. Cross-check BabyBear with gnark-crypto.
- HL instances (BN254 t3, BabyBear t24): `zkhash` at `055bde3f`. Cross-check BabyBear-24 with risc0.
- Avoid leanSpec and ArkLib as oracles.

---

## 6. Is Plonky3 BabyBear-16 the same permutation as HorizenLabs BabyBear-16?

**No.** Shared and differing components:

| Component | HL `POSEIDON2_BABYBEAR_16_PARAMS` | Plonky3 `default_babybear_poseidon2_16()` |
|---|---|---|
| p, d, R_F, R_P | 2013265921, 7, 8, 13 | same |
| Round constants | Grain | **identical**: compared programmatically for t=16 and t=24, including partial-round zero padding |
| M4 in M_E | [[5,7,1,3],[4,6,1,1],[1,3,5,7],[1,1,4,6]] (paper) | **circ(2,3,1,1)** (`MDSMat4`) |
| M_I diagonal (µ−1) | Grain-random (`0x0a632d94, …`) | hand-picked `[-2, 1, 2, 1/2, 3, 4, …]` |

So they share constants but differ in both linear layers. On the Plonky3 input, my reference gives HL-BB16 `[1539913003, 1390604829, …]` and P3-BB16 `[516096821, 90309867, …]`.

The same holds for width 24. Plonky3 BabyBear-24 ≠ HL/risc0 BabyBear-24 (same constants, different M4 and diagonal).

For KoalaBear there is no HL instance. Plonky3 is the de facto definition, but it has two versions (before and after `0056fa83`). Only BN254 t=3 is the same permutation in Plonky3 and HL.

**Implication for naming** (ROADMAP: `Poseidon2.Plonky3.BabyBear.w16` vs `Poseidon2.HorizenLabs.BabyBear.w16`): these really are distinct instances. The parametric spec needs the M4 matrix and the diagonal (µ−1) vector as parameters, not hard-coded. `M_E` for t ∈ {2,3} must also be a parameter, or fixed to circ(2,1)/circ(2,1,1) as HL does, since the paper's text says M_E = M_I.

## Uncertainties

- Section numbers come from the 2024-02-08 ePrint revision; the LNCS version was not checked.
- The Grain description (taps, burn-in, self-shrinking) is taken from the HL sage and Plonky3 Python sources, not from the Poseidon paper text. Plonky3 says it is "Poseidon paper Appendix E"; I did not verify that.
- The 2024 Plonky3 Montgomery scaling (2^-32) is my reading of a comment.
- My HL BabyBear-16 output values are not confirmed upstream; nor are the SP1 and gnark-crypto KoalaBear KAT vintages.
- The SP1 and Aztec internals were only skimmed.
