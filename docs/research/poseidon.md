> **Provenance.** Research notes compiled on 2026-10-12 by Claude Code research agents (see `AI_USE.md`) for Phases 4–5, from the pinned primary sources listed below. Paths such as `scratchpad/scripts/…` and `scratchpad/dl/…` refer to the agents' working files (Python checks and cloned sources), which are not vendored. Where these notes and the Lean specifications disagree, the Lean docstrings, which cite the primary sources, are authoritative.

# Poseidon (circomlib / BN254) — primary-source research for Phase 4

Date: 2026-10-12. Nothing in the repo was edited. All checks below were **executed**, not inferred:
the Python scripts are in `scratchpad/scripts/` (`grain.py`, `ref.py`, `optim.py`, `circomcmp.py`,
`lp.py`, `prs.py`, `crn.py`, `cost.py`), and the cloned sources are in `scratchpad/dl/`.

## 0. Headline results (verified by execution)

1. **All circomlib BN254 Poseidon constants come from the Grain procedure.** This covers every t in 2..17: the round constants C, and the MDS matrix M taken from the *first* Grain-sampled Cauchy matrix, with **no re-sampling**. A ~40-line pure-Python Grain port (`scripts/grain.py`) reproduces `circomlibjs/src/poseidon_constants.json` bit-for-bit for all 16 widths. So the Sage "secure matrix" checks (Alg. 1–3) accepted the first candidate every time.
2. **The optimized tables are a deterministic function of the textbook (C, M).** A Python port of `circomlibjs/tools/poseidon_optimize_constants.js` (`scripts/optim.py`) reproduces `poseidon_constants_opt.js` (C, S, M, P) for all t. Those tables equal `circomlib/circuits/poseidon_constants.circom` (`scripts/circomcmp.py`). `circomlib/circuits/poseidon_constants_old.circom` (the textbook circuit) equals `poseidon_constants.json`.
3. **Textbook and optimized agree on tests.** A textbook implementation (`ref.py`) and the optimized algorithm (`opt` in `ref.py`) agree with each other on random inputs for t=2..17, with all nOut. They also match every published KAT listed in §5.
4. **The round numbers are reproduced.** `hadeshash/code/calc_round_numbers.py` with p = BN254 r, M=128, α=5, followed by "round R_P up to a multiple of t", reproduces circomlib's `N_ROUNDS_P = [56,57,56,60,60,63,64,63,60,66,60,65,70,60,64,68]` exactly (`scripts/crn.py`).

---

## 1. The Poseidon paper: section map

Sources:
- USENIX Security 2021 version: https://www.usenix.org/system/files/sec21-grassi.pdf (pp. 519–535). It has no appendices; it cites the full version as "[30, Appendix X]".
- Full version, ePrint 2019/458: https://eprint.iacr.org/2019/458. eprint.iacr.org returns a Cloudflare 403 to scripts, so I used the Wayback copy `https://web.archive.org/web/2024id_/https://eprint.iacr.org/2019/458.pdf`. That is a 30-page PDF whose metadata says it was built 2023-07-05. **The appendix letters differ between revisions**, as follows:

| Topic | USENIX'21 (body) | ePrint 2019/458 (2023-07 revision) |
|---|---|---|
| Sponge construction | §2.1 (Fig. 1) | §2.1 |
| HADES design strategy; round function ARC → SB → M; R_f full rounds, R_P partial rounds, then R_f full rounds, with R_F = 2R_f (Fig. 2) | §2.2 "The HADES Design Strategy for Hashing" ("Details on the HADES Strategy", "The Round Function") | §2.2 |
| S-box x^α, smallest α with gcd(α, p−1)=1; x^5 for BN254/BLS12-381 | §2.3 "The S-Box Layer" | §2.3 |
| Cauchy MDS M_{i,j} = 1/(x_i + y_j), pairwise-distinct x_i, y_j with x_i + y_j ≠ 0; condition 2t+1 ≤ p | §2.3 "The Linear Layer" | §2.3 |
| "Avoiding Insecure Matrices": subspace S^(i) (Eq. 1); the 3-step method (sample, test with Alg. 1/2/3 of [34], repeat); "For [34, Algorithm 3] we used a search period of l = 4t" | §2.3 | §2.3 |
| Main instances (Table 2: t=3: R_F=8, R_P=57; t=5: R_F=8, R_P=60 for POSEIDON-128) | §4.1 | §4.1 |
| "The round constants and matrices are generated using the Grain LFSR in a self-shrinking mode … described in [30, Appendix F]" | §4.1 | — |
| Domain separation (capacity values; **circomlib does not follow this**) | §4.2 | §4.2 |
| Security claims; statistical/algebraic inequalities: Eq. (2) statistical R_F; Eq. (3) interpolation; Eq. (5) Gröbner (x^α) | §5.2, §5.5.1, §5.5.2 | §5.2, §5.5 |
| Informal Props. 5.1–5.3 (x^5, 256-bit p: R_F = 6, R = 56 + ⌈log_5 t⌉ for 128-bit security) | §5.3 | §5.3 |
| **Security margin: "+2 R_F and +7.5% R_P"** | §5.4 | §5.4 |
| Efficient implementation (equivalent round constants; sparse M' × M'' factorisation, Eq. (5) there) | "[30, Appendix B]" | **Appendix B** |
| Grain LFSR initialisation (b0..b79 layout, taps, discard 160, pair rule, rejection, MSB-first) | "[30, Appendix F]" | **Appendix E** |
| Tables of instances with margin (Table 8, x^5: e.g. t=2/4/6/8/16 → R_P = 56/56/57/57/42) | "[30, Appendix G]" | **Appendix F** (Tables 7, 8) |
| Selecting round numbers in general | — | **Appendix G** |
| Merkle-tree instances | — | Appendix H |

The statistical bound is written two ways:
- The body, Eq. (2), uses C = log2(α−1).
- The 2023 Appendix G, and every script, use C = (α−1)/2.

For α=5 both give C=2. **Uncertainty:** I could not fetch the latest ePrint revision directly, so the appendix letters above are for the 2023-07 build. Cite by title ("Initialization of the Grain LFSR Used for Parameter Generation") to be revision-proof.

**Ordering detail, verbatim from §2.2:** `ARC → SB → M` for every round, including the last. The reference fix of 2021-03-07 added the "final matrix multiplication" that had been missing; see §2.

**The secure-MDS follow-up paper** is Grassi, Rechberger, Schofnegger, "Proving Resistance Against Infinitely Long Subspace Trails: How to Choose the Linear Layer", ToSC 2021(2), ePrint 2020/500. I read the Wayback PDF (39 pp.).
- **Algorithm 1** (invariant trails without active S-boxes) is in §5.1, "Algorithm for Detecting Weak Matrices".
- **Algorithm 2** (invariant trails with active S-boxes) is in §7 / §7.2.1.
- **Algorithm 3** (iterative trails with active S-boxes, period ≤ l) is in **Appendix B**.
- The sufficient condition is **Theorem 8** (§8.1): if the minimal polynomials of M, M², …, M^l all have degree t and are irreducible, then there is no infinitely long subspace trail of period ≤ l. Prop. 13 is the l=1 case.
- The tool linked in the Poseidon paper is https://extgit.iaik.tugraz.at/krypto/linear-layer-tool.

---

## 2. Reference implementation (hadeshash): the exact Grain procedure

- Upstream: `https://extgit.iaik.tugraz.at/krypto/hadeshash.git`. It is clonable anonymously. HEAD is `208b5a164c6a252b137997694d90931b2bb851c5` (2023-05-02, "update Readme"). License: MIT-style (© 2019 Graz University of Technology).
- GitHub mirrors:
  - `dendisuhubdy/hadeshash` @ `659de89cd207e19b92852458dce92adf83ad7cf7` (2021-04-01, "Revert to Version 1.1"; this is also an upstream commit).
  - `daira/pasta-hadeshash` @ `5959f2684a25b372fba347e62467efb00e7e2c3f` (a Pasta fork).
- File: `code/generate_parameters_grain.sage`. It was added in `d9382dbd…` (2020-06-18), was last changed in `95b8cc54…` (2022-07-17), and is now marked "deprecated" in the README (2023-05-02) in favour of `code/generate_params_poseidon.sage`.
- **The Grain, constant, and MDS-sampling code is identical (whitespace-insensitive diff) between the deprecated script and the new `generate_params_poseidon.sage`.** Only the round-number calculation differs. The new script adds a Gröbner-3 bound and the binomial bound from ePrint 2023/537 ("Addition due to https://eprint.iacr.org/2023/537.pdf"), and it computes R_F/R_P itself rather than taking them as arguments.
- Invocation recorded by circomlib, with args `field sbox n t R_F R_P p`:
  `sage generate_parameters_grain.sage 1 0 254 <t> 8 <R_P> 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001`.
  Here FIELD=1 means GF(p), SBOX=0 means "x^alpha", and n=254.

### Initial state (80 bits, MSB-first per field)
```python
bit_list_field = bin(FIELD)[2:].zfill(2)       # b0..b1   : 01  (GF(p))
bit_list_sbox  = bin(SBOX)[2:].zfill(4)        # b2..b5   : 0000 (x^alpha)  <-- NOTE: 0, not "1 for x^5"
bit_list_n     = bin(FIELD_SIZE)[2:].zfill(12) # b6..b17  : 254
bit_list_t     = bin(NUM_CELLS)[2:].zfill(12)  # b18..b29 : t
bit_list_R_F   = bin(R_F)[2:].zfill(10)        # b30..b39 : 8
bit_list_R_P   = bin(R_P)[2:].zfill(10)        # b40..b49 : R_P (AFTER rounding up to a multiple of t)
bit_list_1     = [1] * 30                      # b50..b79
```
**Caveat:** the 2019 usage message, and Filecoin/Neptune's spec, encode the S-box as "0 = x^3, 1 = x^5, 2 = x^-1". So Neptune puts `0001` in b2..b5 for α=5. circomlib (and light-poseidon) used `0` for x^5. Different Poseidon ecosystems therefore have **different constants for the "same" parameters**. Lean must take the 4-bit S-box code as an explicit parameter.

### LFSR, warm-up, and self-shrinking
```python
new_bit = b[62] ^ b[51] ^ b[38] ^ b[23] ^ b[13] ^ b[0]; b.pop(0); b.append(new_bit)
```
That is, b_{i+80} = b_{i+62} ⊕ b_{i+51} ⊕ b_{i+38} ⊕ b_{i+23} ⊕ b_{i+13} ⊕ b_i.
- Clock it 160 times and discard the output.
- Then repeat: clock to get bit₁, clock to get bit₂; if bit₁ = 1, output bit₂, otherwise discard both.

The Sage code is written as a nested `while new_bit == 0` loop, but it is equivalent to this pair rule. It is verified equivalent because my pair-rule port reproduces all the constants.

### Sampling
- `grain_random_bits(n)`: take n output bits; the **first bit is the MSB** (`int("".join(bits), 2)`).
- Round constants: `num_constants = (R_F + R_P) * t`. Each is `rnd(254)`, re-drawn **while ≥ p** (rejection sampling). The flat index is `r*t + i` (round-major).
- **Order: all round constants first, then the MDS matrix**, drawn from the same continuing stream.

### MDS sampling
```python
rand_list = [F(grain_random_bits(n)) for _ in range(0, 2*t)]   # F(.) REDUCES mod p -- no rejection here!
while len(rand_list) != len(set(rand_list)):                   # all 2t distinct, else redraw all 2t
    rand_list = [F(grain_random_bits(n)) for _ in range(0, 2*t)]
xs = rand_list[:t]; ys = rand_list[t:]
M[i, j] = (xs[i] + ys[j])^(-1)                                  # PLUS, not minus; restart if any xs[i]+ys[j]==0
```
- Then `generate_matrix` loops: `while algorithm_1 or algorithm_2 or algorithm_3 fails: M = create_mds_p(...)`.
  - The script's `algorithm_1` is a simplified check: M^i not scalar; no eigenspace ∩ S^(i) of M^i for i ≤ t−1; S^(i) not invariant.
  - `algorithm_2` handles invariant trails with an active S-box.
  - `algorithm_3` applies `algorithm_2` to M^r for r = 2..4t.
  - They need Sage eigenspaces over F_p, including over extensions (`format='galois'`).
- **For circomlib BN254, the first sample passed for every t = 2..17** (verified: attempt 1 matches).
- MDS orientation: the reference does `state = M * state` (column vector). In `poseidon_constants.json`, `M[t-2][i][j]` is row i, used as `new[i] = Σ_j M[i][j]·s[j]` (circomlibjs `poseidon_reference.js`).

### History that matters for compatibility
- hadeshash README, "Update from 07/03/2021": "the linear layer was computed as state = state * M instead of M * state, and … the final matrix multiplication was missing."
- circomlib followed the next day: commit `cf853c1cc96fa537cb1030f70a6f78e5d80ed0e4` (2021-03-08, "poseidonfix"). It switched to `M[i][j]`, kept the last-round MDS, and moved the capacity to state[0] (`[F.zero, ...inputs]` instead of `[...inputs, F.zero]`).
- Grain constants entered circomlib in `86c6a2a6f5e8de4024a8d366eff9e35351bc1a2e` (2020-08-09, "New Version of Poseidon"). Before that, Poseidon was blake2b-based (2019).
- `a86654785d06…` (2021-07-12) extended it to 16 inputs. `ddea7da37664…` (2021-10-04) added the optimization. `db02024107…` (2022-06-17) added PoseidonEx.
- **Pre-2021-03 circomlib hashes differ from today's.**

### Reference test vectors (`code/test_vectors.txt` @ 208b5a16)
These are permutation outputs on input [0,1,2] and [0,1,2,3,4]:
- poseidonperm_x5_254_3: out[0] = `0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a`, out[1] = `0x0fca49b798923ab0239de1c9e7a4a9a2210312b6a2f616d18b5a87f9b628ae29`, out[2] = `0x0e7ae82e40091e63cbd4f16a6d16310b3729d4b6e138fcf54110e2867045a30c`
- poseidonperm_x5_254_5: out[0] = `0x299c867db6c1fdd79dcefa40e4510b9837e60ebb1ce0663dbaa525df65250465`, out[1] = `0x1148aaef609aa338b27dafd89bb98862d8bb2b429aceac47d86206154ffe053d`, out[2] = `0x24febb87fed7462e23f6665ff9a0111f4044c38ee1672c1ac6b0637d34f24907`, out[3] = `0x0eb08f6d809668a981c186beaf6110060707059576406b248e5d9cf6e78b3d3e`, out[4] = `0x07748bc6877c9b82c8b98666ee9d0626ec7f5be4205f79ee8528ef1c4a376fc7`

These coincide with circomlib `poseidon([1,2])` and `poseidon([1,2,3,4])`. The `poseidonperm_x5_254_3.sage` MDS row 0 (`0x109b7f41…`) equals circomlibjs `M[1][0]`. So the IAIK reference instance for t=3/5 **is** the circomlib instance: IAIK's own KATs are a second-party oracle for t=3 and t=5.

---

## 3. circomlib / circomlibjs Poseidon over BN254

Repos and licences:
- `iden3/circomlib` @ `35e54ea21da3e8762557234298dbb553c175ea8d` (2025-04-03), v2.0.5, **LGPL-3.0** (circuits).
- `iden3/circomlibjs` @ `48b3ab37013c5ed21e9ff8a80a5b010795c97094` (2025-04-04), v0.1.8, **GPL-3.0**.

The JS was moved out of circomlib in circomlibjs `3d29629a…` (2021-10-06, "Transfer from circomlib").

### Parameters
- **t = 2..17**, i.e. nInputs 1..16: `N_ROUNDS_P` has 16 entries, and `POSEIDON_C/M/P/S(t)` have branches t==2..17. This applies to `circuits/poseidon.circom`, `poseidon_old.circom`, circomlibjs, and go-iden3-crypto.
- R_F = 8 for all t.
- `N_ROUNDS_P = [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68]` for t = 2..17.
- Unrounded `calc_round_numbers.py` output (M=128, BN254 p): R_P = 56 for t=2..5 and 57 for t=6..17. Rounding up to a multiple of t gives the list above (verified).
- α = 5 (`pow5`, `Sigma`). p = 21888242871839275222246405745257275088548364400416034343698204186575808495617.

### Provenance comments in the code
- In `circomlibjs/src/poseidon_reference.js`, `poseidon_opt.js`, and `circomlib/circuits/poseidon_constants*.circom`: "Parameters are generated by a reference script …/generate_parameters_grain.sage. Used like so: sage generate_parameters_grain.sage 1 0 254 2 8 56 0x3064…0001".
- In `poseidon_opt.js`: "Optimization is taken from https://github.com/filecoin-project/neptune".
- Generator for the optimized tables: `circomlibjs/tools/poseidon_optimize_constants.js` (reads `src/poseidon_constants.json`, writes `src/poseidon_constants_opt.js`).
- There is no `calcposeidonconstants` script in circomlib. The textbook C, M were pasted from Sage output.
- Also in circomlibjs: `src/poseidon_gencontract.js` (EVM bytecode generator, uses the textbook C, M) and `src/poseidon_wasm.js`.

### Textbook algorithm (`circomlibjs/src/poseidon_reference.js`)
```js
let state = [initState, ...inputs];               // t = inputs.length + 1; initState default 0
for (r = 0; r < RF + RP; r++) {
  state[i] += C[t-2][r*t + i];                    // ARC
  if (r < RF/2 || r >= RF/2 + RP) state = state.map(pow5); else state[0] = pow5(state[0]);
  state[i] = Σ_j M[t-2][i][j] * state[j];         // MDS on every round, incl. the last
}
return nOut == 1 ? state[0] : state.slice(0, nOut);
```

### Optimized algorithm (`circomlibjs/src/poseidon_opt.js` ≡ `circomlib/circuits/poseidon.circom` `PoseidonEx`)

Notation: textbook constants c_r ∈ F^t for r = 0..R−1 (R = R_F + R_P), MDS M (column convention `x ↦ M x`), h = R_F/2 = 4. The tables are stored in **row-vector convention**: the opt table `M_opt = Mᵀ`, and `Mix` computes `out[i] = Σ_j M_opt[j][i]·in[j]`, which equals `(M·in)[i]`. Index layout of `C_opt` (length `t·R_F + R_P`):

```
s ← s + C_opt[0..t)                                         // = c_0
for r in 0..h-2:  s ← S(s);  s ← s + C_opt[(r+1)t ..+t];  s ← M s        // C_opt block = M⁻¹ c_{r+1}
s ← S(s);  s ← s + C_opt[h·t ..+t];  s ← P s                              // last first-half full round
for r in 0..R_P-1:                                                        // partial rounds
   s0 ← s0^5 + C_opt[(h+1)t + r]                                          // ONE scalar constant
   s  ← Sparse_r(s)        // new s0 = Σ_j S[(2t-1)r + j]·s_j ;  s_k += s0_old·S[(2t-1)r + t + k − 1], k ≥ 1
for r in 0..h-2:  s ← S(s);  s ← s + C_opt[(h+1)t + R_P + r·t ..+t];  s ← M s
s ← S(s);  s ← M s                                                        // final round: NO constant
```

**How C_opt is derived** (`convertConstants` in `tools/poseidon_optimize_constants.js`; ported in `scripts/optim.py`, exact match):
- Because S(x) + … then M, and `M(y) + c = M(y + M⁻¹c)`, every full-round constant after the first is replaced by `M⁻¹ c_{r+1}` and added *after* the S-box of the previous round. The last round's constant is consumed this way, so the final round adds none.
- Partial-round constants are pushed backwards. Start with acc := c_{h+R_P} (the first second-half constant). For r = h+R_P−1 down to h:
  - a := M⁻¹ acc
  - emit scalar a[0]
  - set a[0] := 0
  - acc := a + c_r
- Then C_opt block h = M⁻¹ acc (one full vector, added after the S-box of the last first-half round), followed by the R_P emitted scalars in forward order.
- This is the "Round Constants" paragraph of Poseidon full version **Appendix B**: "move parts of the original round constants from the last round all the way through … one constant applied to the entire state after the first R_f full rounds".

**How S and P are derived** (`sparseFactorize` and `calculatePS`):
- Paper App. B, Eq. (5): write `M = [[M00, v],[w, M̂]]`. Then `M = M' × M''` with `M' = [[1,0],[0,M̂]]` and `M'' = [[M00, v],[ŵ, I]]`, where `ŵ = M̂⁻¹ w`.
- Since M' acts as the identity on word 0, it commutes with the partial S-box and the scalar constant. It is pushed backwards and absorbed into the previous round's matrix.
- The code (in Mᵀ / row-vector form) iterates m₀ = Mᵀ. For each of the R_P partial rounds: factor m_i = mp_i · Sp_i, record Sp_i, set m_{i+1} = Mᵀ · mp_i.
- After R_P steps, `P := m_{R_P}`, which replaces the MDS of the last first-half full round. The recorded sparse matrices are emitted in **reverse** order (S block r = factor recorded at step R_P−1−r).
- Each block is `[M00, ŵ_0..ŵ_{t-2}, v_1..v_{t-1}]` (2t−1 elements). In the column convention the sparse matrix is `[[M00, v],[ŵ, I]]` transposed appropriately. MixS computes `new s0 = M00 s0 + Σ ŵ_{k-1} s_k` and `s_k += v_k s0`, so it is the row-vector form of `[[M00 | ŵ ],[v | I]]`. **Be careful with the transpose when formalising**: the code's `S` packs (M00, ŵ = M̂⁻¹w, then the first row of Mᵀ without M00).

Other independent write-ups of the same derivation:
- Filecoin/Neptune spec `spec/poseidon_spec.md`, sections "Optimized Round Constants", "Sparse MDS Matrices", "Optimized Poseidon", in `argumentcomputer/neptune` (formerly `filecoin-project/neptune`, `lurk-lab/neptune`) @ `b06f03c5abcb6ff72625349572b21241956d55df`.
- The `poseidonperm_x3_64_24_optimized.sage` file in hadeshash.

**Do not use Neptune's constants:** Neptune uses SboxBits=0001, n=255 (BLS12-381), and a *deterministic* Cauchy matrix x=[0..t−1], y=[t..2t−1]. Its spec §"MDS Matrix" is a different instance family.

Remark on the "2023 paper on optimized Poseidon": I did not find a separate 2023 primary source specific to circomlib's scheme. The canonical citations are Poseidon App. B (which itself cites the LowMC trick, [DKP+19]) and the Neptune spec.

---

## 4. circomlib hashing convention (sponge)

From `circuits/poseidon.circom`:
```circom
template Poseidon(nInputs) {           // t = nInputs + 1
    pEx.initialState <== 0;            // state[0] = capacity = 0
    pEx.inputs[i] <== inputs[i];       // state[1..t) = inputs
    out <== pEx.out[0];                // output = state[0] AFTER the permutation
}
```
In `PoseidonEx`, `ark[0].in[0] <== initialState; ark[0].in[j] <== inputs[j-1]`, and `out[i] = MixLast(t,M,i)`, i.e. the first nOuts words.

circomlibjs `poseidon(inputs, initState=0, nOut=1)` behaves the same way: `state=[initState,...inputs]` and returns `state[0]`, or `slice(0,nOut)`.

So: **single permutation call, no padding, no length/domain tag, capacity element = word 0 = 0, output = word 0** (the capacity word, not a rate word as in the paper's §2.1). This is a fixed-arity compression function, not a sponge, and it does **not** follow paper §4.2 domain separation. Inputs must be < p; circomlibjs `F.e` reduces mod p, while light-poseidon rejects inputs ≥ p.

---

## 5. Known-answer vectors (all re-verified with `scripts/ref.py`)

Notation: H(x₁..x_n) = circomlib `poseidon([x₁..x_n])`, so t = n+1 and initState = 0.

| inputs | output | source |
|---|---|---|
| [1] (t=2) | 18586133768512220936620570745912940619677854269274689475585506675881198879027 = 0x29176100eaa962bdc1fe6c654d6a3c130e96a4d1168b33848b897dc502820133 | circomlibjs test/poseidon.js; go-iden3-crypto; poseidon-rs; light-poseidon TEST_CASES[0] |
| [1,2] (t=3) | 7853200120776062878684798364095072458815029376092732009249414926327459813530 = 0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a | circomlibjs; circomlib test/poseidoncircuit.js; hadeshash test_vectors.txt |
| [3,4] (t=3) | 14763215145315200506921711489642608356394854266165572616578112107564877678998 | circomlib test/poseidoncircuit.js |
| [1,1] (t=3) | 0x007af346e2d304279e79e0a9f3023f771294a78acb70e73f90afe27cad401e81 | light-poseidon tests |
| [0x0101…01 (32 bytes), 0x0202…02] (t=3) | 0x0d54e1938f8a8c1c7deb5e0355f26319207b84fe9ca2ce1b26e735c829821990 | light-poseidon README + tests |
| [1,2,3,4] (t=5) | 0x299c867db6c1fdd79dcefa40e4510b9837e60ebb1ce0663dbaa525df65250465 | circomlibjs; hadeshash |
| [1,2,0,0,0] (t=6) | 1018317224307729531995786483840663576608797660851238720571059489595066344487 | circomlib circuit test; go-iden3-crypto; poseidon-rs |
| [3,4,0,0,0] (t=6) | 5811595552068139067952687508729883632420015185677766880877743348592482390548 | go-iden3-crypto; poseidon-rs |
| [3,4,5,10,23] (t=6) | 13034429309846638789535561449942021891039729847501137143363028890275222221409 | circomlib circuit test |
| [1,2,0,0,0,0] (t=7) | 15336558801450556532856248569924170992202208561737609669134139141992924267169 | go-iden3-crypto; poseidon-rs |
| [3,4,0,0,0,0] (t=7) | 12263118664590987767234828103155242843640892839966517009184493198782366909018 | go-iden3-crypto; poseidon-rs |
| [1..6] (t=7) | 20400040500897583745843009878988256314335038853985262692600694741116813247201 | circomlibjs; go-iden3-crypto; poseidon-rs |
| [1..14] (t=15) | 8354478399926161176778659061636406690034081872658507739535256090879947077494 | go-iden3-crypto; poseidon-rs |
| [1..9,0×5] (t=15) | 5540388656744764564518487011617040650780060800286365721923524861648744699539 | go-iden3-crypto; poseidon-rs |
| [1..9,0×7] (t=17) | 11882816200654282475720830292386643970958445617880627439994635298904836126497 | circomlibjs; go-iden3-crypto; poseidon-rs |
| [1..16] (t=17) | 9989051620750914585850546081941653841776809718687451684622678807385399211877 | circomlibjs; go-iden3-crypto; poseidon-rs |
| initState=7, [1,2,3,4] | 1569211601569591254857354699102545060324851338714426496554851741114291465006 | circomlibjs |
| initState=17, [1..16] | 7865037705064445207187340054656830232157001572238023180016026650118519857086 (+15 more outputs in the test) | circomlibjs |
| nOut=2, [1,2] | [7853200…813530, 7142104613055408817911962100316808866448378443474503659992478482890339429929] | circomlibjs; go-iden3-crypto |
| nOut=3, [1,2,0,0,0] | [1018317…344487, 1268987460374965117190107941866588409937190018195924754936306024116268626868, 8783366202813713093021184624438037804022412226788318946130389248546914776762] | circomlibjs |
| nOut=11, [1..16] | 11 values in circomlibjs test/poseidon.js "Should check poseidon with n outputs" | circomlibjs; go-iden3-crypto |

**light-poseidon `TEST_CASES`, H([1]×n) for n = 1..12** (`light-poseidon/tests/bn254_fq_x5.rs`; per the comment, "created with circomlibjs"):
```
n=1  0x29176100eaa962bdc1fe6c654d6a3c130e96a4d1168b33848b897dc502820133
n=2  0x007af346e2d304279e79e0a9f3023f771294a78acb70e73f90afe27cad401e81
n=3  0x02c0066e10a72abd2b33c3b214cb3e81bcb1b6e30961cd23c202b18673bf2543
n=4  0x082c9c370a0d24f4416fbc414a37681f78442d27d86385991c17d6fc0c4b7d71
n=5  0x10389605ae688d4f14db853122c47d66a803c72b41589cb1bf868741b206b9bb
n=6  0x2a73f679328c3eab724aa3e5bdbf50b39035d7729f135b9709890f85c5dc5e76
n=7  0x2276310aa7f3343a284214139d9da959be2a31b2c708a5f81954b265e53a30b8
n=8  0x177e1453c446e1b07d2b4233425147095c4fcabb233d230b6d46a214d95b2884
n=9  0x0e8fee2fe49da30fdeeb48c42ebb44cc6ee7055f61fbca5e313b8a5fca834c47
n=10 0x2ec4c65e6378ab8c7330854f4a7077c1ff9260e44885c4b81dd131ad3a86cd96
n=11 0x00713d41eca635f117d4ecbceb5f3a66dc4142eb70b56765bc358f1bec40bb9b
n=12 0x14390be0baef249bd47c65ddac65c2e52e8513c081c1cd72c98006098e9a8fbe
```

Derived by my Python port only, **not** from an external source (use for cross-checks, not as provenance):
- H([1]×13..16) = 0x2ebd80a1…5c6c, 0x262ac449…e9dd, 0x1be1d1af…cd3d, 0x23eb8f6f…d38e
- H([1..n]) for n=3,5,7..13,15: see the `prs.py` output (e.g. n=3: 0x0e7732d89e6939c0ff03d5e58dab6302f3230e269dc5b968f725df34ab36d732)

Source URLs and commits:
- https://github.com/iden3/circomlibjs/blob/48b3ab37013c5ed21e9ff8a80a5b010795c97094/test/poseidon.js
- https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/test/poseidoncircuit.js
- https://github.com/iden3/go-iden3-crypto/blob/4c63aa32ab1f2a4ff949aa81bbb90b8533e66df6/poseidon/poseidon_test.go
- https://github.com/arnaucube/poseidon-rs/blob/f4ba1f7c32905cd2ae5a71e7568564bb150a9862/src/lib.rs (`test_hash`). Note that some decimal comments there are copy-pasted; the hex strings are what is asserted.
- https://github.com/Lightprotocol/light-poseidon/blob/5a796b5f8d20776729599a0635470551f205319e/light-poseidon/tests/bn254_fq_x5.rs
- https://extgit.iaik.tugraz.at/krypto/hadeshash/-/blob/208b5a164c6a252b137997694d90931b2bb851c5/code/test_vectors.txt

Larger official vector sets: none beyond these. There are no bulk KAT files (no random-input corpus) in iden3, Light, or IAIK. For bulk testing, generate vectors from an oracle crate (§6).

---

## 6. Rust oracle crates (circom-compatible BN254)

| crate | latest | licence | t supported | algorithm | constants source | independence |
|---|---|---|---|---|---|---|
| **light-poseidon** (Lightprotocol/light-poseidon @ `5a796b5f8d20776729599a0635470551f205319e`) | 0.4.1 (crates.io, 12.9M downloads), arkworks 0.5 (`ark-bn254`, `ark-ff`) | Apache-2.0 | **t = 2..13** (inputs 1..12; `new_circom(n)`); generic `PoseidonParameters` for others | **textbook** (ARC/S-box/MDS per round); supports a domain tag in state[0] | `xtask/src/generate_parameters.rs` **clones hadeshash and runs the Sage script** (`1 0 254 t 8 R_P p`) for t=2..13 | Independent of circomlibjs code and constants (it regenerates from Sage); tests compare against circomlibjs outputs. Audited (`assets/audit.pdf`, Veridise per the README; not opened). |
| **poseidon-rs** (arnaucube/poseidon-rs @ `f4ba1f7c32905cd2ae5a71e7568564bb150a9862`, 2023-05-11) | 0.0.10 | Apache-2.0 | **t = 2..17** | **textbook** | `src/constants.rs`: decimal strings, the same values as circomlib's `poseidon_constants.json` (iden3 author) | Independent code; constants copied from iden3 (not regenerated). Uses the old `ff_ce` 0.11. Low maintenance. Arkworks sibling `arnaucube/poseidon-ark` (GitHub only, Apache-2.0). |
| zkhash (HorizenLabs/poseidon2 @ `055bde3f4782731ba5f5ce5888a440a94327eaf3`, `plain_implementations/`) | 0.2.0 | MIT OR Apache-2.0 | Poseidon BN256: **t=3 only, R_P = 56**, its own MDS/RC (`poseidon_instance_bn256.rs`; first RC 0x2c4c51fd…) | textbook + optimized | own Sage run | **NOT circomlib-compatible** (circomlib t=3 uses R_P=57; the constants differ). Useful only for Poseidon2. |
| soroban-poseidon (stellar/rs-soroban-poseidon) | 28.0.0 | Apache-2.0 | claims circomlib-compatible BN254 | sponge | — | Tied to the Soroban host env; poor oracle. |
| neptune (argumentcomputer) | 13.0.0 | MIT/Apache | BLS12-381 Filecoin instances | optimized | own (SboxBits=1, deterministic MDS) | Not circomlib-compatible. |

Non-Rust, but an independent implementation of the *optimized* algorithm: **go-iden3-crypto** `poseidon/` (Go, Apache-2.0, @ `4c63aa32ab1f2a4ff949aa81bbb90b8533e66df6`), t=2..17, with C/S/M/P tables.

Recommendation:
- Use **light-poseidon** as the primary Rust oracle. Its constants are independently regenerated from the IAIK Sage script, and its algorithm is textbook.
- Use **poseidon-rs** as a second, code-independent oracle covering t = 14..17. Its constants are shared with circomlib.
- Neither wraps the other.

---

## 7. Table sizes and feasibility of Grain inside Lean

Per t, for BN254 with R_F = 8 (verified counts):

| t | R_P | textbook C = (8+R_P)·t | M = t² | opt C = 8t+R_P | opt S = R_P(2t−1) | opt M+P = 2t² | LFSR clocks to derive C and M |
|---|---|---|---|---|---|---|---|
| 2 | 56 | 128 | 4 | 72 | 168 | 8 | 185,258 |
| 3 | 57 | 195 | 9 | 81 | 285 | 18 | 276,412 |
| 5 | 60 | 340 | 25 | 100 | 540 | 50 | 491,324 |
| 9 | 63 | 639 | 81 | 135 | 1071 | 162 | 869,712 |
| 13 | 65 | 949 | 169 | 169 | 1625 | 338 | 1,291,500 |
| 17 | 68 | 1292 | 289 | 204 | 2244 | 578 | 1,749,906 |
| **Σ t=2..17** | | **12,638 elements (textbook C+M)** | | **24,060 elements (opt C+S+M+P)** | | | **14.8 M clocks total** |

The full per-t table is in `scripts/cost.py`'s output. p/2^254 ≈ 0.756, so about 32% of 254-bit draws are rejected (e.g. 70 rejections for t=3). Each output bit costs 4 clocks on average.

Feasibility:
- Evaluating Grain is ~10⁵–10⁶ bit-steps per t, and 1.5·10⁷ for all t. It is cheap with `native_decide` / compiled evaluation, and probably too heavy for `decide` or `rfl` in the kernel at that size if bits are lists (see below).
- A kernel `rfl` over GMP-accelerated `Nat` with the 80-bit state packed into one `Nat` (shift/xor/testBit are GMP-accelerated in the kernel) is plausibly feasible per t. Each t needs ~2–3·10⁵ iterations of a few Nat ops. **This is untested.** Treat it as a risk and prototype t=2 first.
- The M step needs 2t samples, a distinctness check, and t² field inversions, which are cheap.
- The **secure-matrix checks (Alg. 1–3: eigenspaces over F_p and extensions, powers up to M^{4t})** are not practical to replicate in Lean. They are also unnecessary for circomlib, since the first sample was accepted for every t. Options:
  1. Define the spec constant as "the first Grain Cauchy sample" and prove equality to the tables.
  2. Additionally state a Theorem-8-style property (irreducible minimal polynomial of M^k) as an unverified or checked-by-certificate side fact.
- The optimized tables are derived from (C, M) by a few hundred matrix inversions and products over F_p per t. The derivation itself should be **proved** generically (App. B algebra) rather than evaluated. The concrete equality `opt tables = convert(C, M)` can then be checked by evaluation.

## Uncertainties / not verified
- The latest ePrint revision of 2019/458 was not fetched directly (Cloudflare). Appendix letters are from the 2023-07 Wayback build.
- I did not run Sage, so the secure-matrix acceptance is inferred from "first sample matches". That is logically sufficient, because the Sage loop returns the first matrix that passes.
- The light-poseidon audit PDF was not opened.
- Kernel-evaluation cost of Grain in Lean is an estimate.
