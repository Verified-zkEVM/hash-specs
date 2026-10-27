# Poseidon2

Poseidon2 is the permutation of *Poseidon2: A Faster Version of the Poseidon Hash Function* by
Grassi, Khovratovich and Schofnegger [Grassi et al. 2023]. It keeps the HADES structure of
Poseidon [Grassi et al. 2021] (full rounds at each end, partial rounds in the middle) but replaces
the linear layers with ones that cost $O(t)$ operations instead of $O(t^2)$. Poseidon2 is used in
STARK systems over 31-bit fields (Plonky3 and the systems built on it, such as SP1 and OpenVM, and
RISC Zero) and over BN254 (for example in Noir's standard library). As with Poseidon,
implementations differ in their matrices and constants, so "Poseidon2" names a family, and each
instance here is named after its source. This directory provides HorizenLabs' BN254 instance of
width 3 [HorizenLabs] and Plonky3's BabyBear and KoalaBear instances of widths 16 and 24 [Plonky3],
together with Plonky3's padding-free sponge and truncated-permutation compression over them. It
contains a reference specification that follows the paper, with the matrices as parameters; an
executable specification that computes the linear layers as the implementations do; and a proof
that the two agree. Section numbers such as §6 refer to the full version of the paper, ePrint
2023/323, revision of 2024-02-08.

## Notation

- $\mathbb{F}_p$ is the prime field. The reference works in any commutative ring `F`; the
  instances take `ZMod p`. A *state* is a vector of $t$ elements, `Vector F t`.
- $d$ is the S-box exponent: the S-box is $x \mapsto x^d$ (`Hash.ZK.sbox`), a permutation of
  $\mathbb{F}_p$ when $\gcd(d, p - 1) = 1$ [Grassi et al. 2023, §6]. It is shared with Poseidon;
  see [`../Poseidon/README.md`](../Poseidon/README.md).
- $R_F$ is the number of external (full) rounds, half before and half after the $R_P$ internal
  (partial) rounds.
- $M_E$ and $M_I$ are the external and internal matrices. $\mathrm{circ}(a_0, \dots, a_{n-1})$
  is the circulant matrix with first row $(a_0, \dots, a_{n-1})$, each row the previous one
  rotated right by one. $J$ is the all-ones matrix and $\mathrm{diag}(v)$ the diagonal matrix
  with entries $v_i$.
- $M_4$ is a fixed $4 \times 4$ MDS matrix from which $M_E$ is built for widths that are
  multiples of 4.

## Parameters

| Instance          | Field $p$                       | $t$    | $d$ | $R_F$ | $R_P$   | $M_4$                  |
|-------------------|---------------------------------|--------|-----|-------|---------|------------------------|
| HorizenLabs BN254 | BN254 scalar field (`bn254`)    | 3      | 5   | 8     | 56      | none: $M_E = \mathrm{circ}(2,1,1)$ |
| Plonky3 BabyBear  | $2^{31} - 2^{27} + 1$ (`babyBear`) | 16, 24 | 7   | 8     | 13, 21  | $\mathrm{circ}(2,3,1,1)$ |
| Plonky3 KoalaBear | $2^{31} - 2^{24} + 1$ (`koalaBear`) | 16, 24 | 3   | 8     | 20, 23  | $\mathrm{circ}(2,3,1,1)$ |

In Lean the generic parameters are `Hash.ZK.Poseidon2.Params F t` (fields `α`, `RF`, `RP`, `CE`,
`CI`, `ME`, `MI`). A Plonky3 instance is a `Plonky3` record (field size, exponent, width, $R_P$,
internal diagonal); the four in use are `babyBear16`, `babyBear24`, `koalaBear16` and
`koalaBear24`, and `Plonky3.params` turns one into reference parameters over `ZMod p`. The BN254
instance's parameters are `hlBn254Params`. The primes are in `Hash/ZK/Common/Primes.lean`.

**Internal diagonals.** For BN254, $M_I = [[2,1,1],[1,2,1],[1,1,3]]$, that is
$J + \mathrm{diag}(1, 1, 2)$ [HorizenLabs, `poseidon2_instance_bn256.rs`]. Plonky3's diagonals
$v$ are hand-picked dyadic rationals $\pm a / 2^b$ (small integers such as $-2, 1, 2, 3, 4$ and
inverse powers of two such as $1/2^8$, $-1/2^{27}$), chosen so that each multiplication is cheap.
They are transcribed from Plonky3's source code as `babyBearDiag16`, `babyBearDiag24`,
`koalaBearDiag16` and `koalaBearDiag24`, lists of `Dyadic`.

## The permutation

The permutation [Grassi et al. 2023, §6] first multiplies the state by $M_E$, then applies
$R_F/2$ external rounds, $R_P$ internal rounds and $R_F/2$ external rounds:

$$P_2(x) = \mathcal{E}_{R_F-1} \circ \cdots \circ \mathcal{E}_{R_F/2} \circ
\mathcal{I}_{R_P-1} \circ \cdots \circ \mathcal{I}_0 \circ
\mathcal{E}_{R_F/2-1} \circ \cdots \circ \mathcal{E}_0 (M_E \cdot x).$$

**External round** $r$ (`Reference.externalRound`): add a constant to every element, apply the
S-box to every element, multiply by $M_E$:

$$\mathcal{E}_r(x) = M_E \cdot \big((x_0 + c^{(r)}_0)^d, \dots, (x_{t-1} + c^{(r)}_{t-1})^d\big).$$

**Internal round** $r$ (`Reference.internalRound`): add a single constant to the first element,
apply the S-box to it alone, multiply by $M_I$:

$$\mathcal{I}_r(x) = M_I \cdot \big((x_0 + \hat c^{(r)})^d, x_1, \dots, x_{t-1}\big).$$

Two changes from Poseidon: the initial multiplication by $M_E$ [Grassi et al. 2023, §4], and the
single constant per internal round [Grassi et al. 2023, §6]. The whole is
`Reference.permutation`.

## The linear layers

**External matrix** [Grassi et al. 2023, §5.1]. For widths $t = 4k \ge 8$,

$$M_E = \mathrm{circ}(2 M_4, M_4, \dots, M_4):$$

the state splits into blocks of four, and block $(a, b)$ of the matrix is $2 M_4$ when $a = b$
and $M_4$ otherwise (`blockCirculant`). The paper's $M_4$ is
$[[5,7,1,3],[4,6,1,1],[1,3,5,7],[1,1,4,6]]$; Plonky3's 31-bit instances use
$\mathrm{circ}(2, 3, 1, 1)$ instead (`plonky3M4`). For widths 2 and 3 the implementations take
$\mathrm{circ}(2, 1)$ and $\mathrm{circ}(2, 1, 1)$ (`externalSmall`), while the paper's text sets
$M_E = M_I$ [Grassi et al. 2023, §6]. The specification follows the implementations.

**Internal matrix** [Grassi et al. 2023, §5.2]. $M_I = J + \mathrm{diag}(v)$
(`onesPlusDiag`), so the paper's diagonal entries are $\mu_i = 1 + v_i$. Multiplying by it costs
one sum and $t$ multiplications:

$$y_i = v_i \cdot x_i + \sum_j x_j.$$

**Fast layers** [Grassi et al. 2023, §5, App. B]. The fast specification (`Fast.lean`) computes
the layers this way rather than as matrix–vector products: for widths 2 and 3 it adds the sum of
the state to every element (`Fast.externalSmall`); for $t = 4k$ it multiplies each block by
$M_4$ and adds to every element the sum of the elements at the same position in all blocks
(`Fast.externalM4`); the internal layer is `Fast.internal`. `Fast.externalSmall_eq`,
`Fast.externalM4_eq` (the block-reindexing argument for $\mathrm{circ}(2 M_4, M_4, \dots)$) and
`Fast.internal_eq` prove that these are the matrix products.

## Constants

The round constants come from the Grain LFSR shared with Poseidon (`Hash/ZK/Common/Grain.lean`;
see [`../Poseidon/README.md`](../Poseidon/README.md)), initialised with field type 1, S-box code
0, the field size $n$ in bits, the width and the round numbers. The paper says only that they are
"generated as in Poseidon" [Grassi et al. 2023, §6]; the order comes from HorizenLabs' generation
script `poseidon2_rust_params.sage`. That order is the $R_F/2 \cdot t$ constants of the initial
external rounds, then the $R_P$ internal constants, then the $R_F/2 \cdot t$ constants of the
final external rounds (`grainSamples`). Plonky3's BabyBear constants are those of HorizenLabs;
its KoalaBear instance has no HorizenLabs counterpart.

Plonky3 releases before 0.6 drew the KoalaBear constants in a different order (initial, final,
internal). Those releases compute a different permutation under the same name. This library
follows the corrected order of Plonky3 commit `0056fa83`, which Plonky3 0.8.0 ships.

**Example.** HorizenLabs' BN254 instance maps the state $[0, 1, 2]$ to

```
0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033
0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570
0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8
```

This is the vector of HorizenLabs' reference implementation (`poseidon2_tests_bn256::kats` in
`zkhash`), and the fast permutation `Fast.permutation (hlBn254FastParams (ZMod bn254))` computes
it. Since the fast permutation is proved equal to the reference, it is also the output of
`hlBn254Permutation`.

## Sponge and compression

Plonky3 builds its Merkle-tree hash and compression functions from the permutation
(`Hash/Construction/FieldSponge.lean`, `Sponge.lean`):

- **Padding-free sponge** (`Hash.FieldSponge.paddingFree`, `Plonky3.sponge`) [Plonky3,
  `PaddingFreeSponge`]. From the zero state of $t$ elements, each block of `rate` input elements
  overwrites the start of the state, which is then permuted; a final partial block overwrites
  only its own positions, and an empty final block is not absorbed. The digest is the first
  `out` elements. Plonky3 typically uses rate 8 at width 16 and rate 16 at width 24, with output 8.
- **Truncated-permutation compression** (`Hash.FieldSponge.truncatedPermutation`,
  `Plonky3.compress`) [Plonky3, `TruncatedPermutation`]. Place the inputs (typically two chunks
  of 8) at the start of the zero state, permute, and keep the first `chunk` elements.

`Hash.FieldSponge.onList` turns a permutation of vectors into one on lists. There is no padding,
so the sponge is collision resistant only for inputs of a fixed length (Merkle leaves, trace
rows). `Hash.FieldSponge.absorb_append` proves that absorbing a block-aligned prefix and then the
rest gives the state of absorbing everything, so an incremental implementation agrees with the
one-shot definition.

## Security notes

This section points to the literature; it makes no claims of its own.

- **Round numbers.** Poseidon2 keeps Poseidon's round numbers. The paper argues that the new
  linear layers give the same security against statistical and algebraic attacks
  [Grassi et al. 2023, §7]. The initial multiplication by $M_E$ is there because, otherwise, the
  first round's linear layer could be peeled off: a permutation used in a sponge should start and
  end with a linear layer [Grassi et al. 2023, §4].
- **Internal matrix.** The diagonal must be chosen so that no subspace trail passes through
  arbitrarily many internal rounds. The paper gives a sufficient condition on the minimal
  polynomials of $M_I$ and its powers [Grassi et al. 2023, §5.3]. Plonky3 documents its check of
  this condition for its hand-picked diagonals.
- **Cryptanalysis.** The attacks of Bariant, Bouvier, Leurent and Perrin on round-reduced
  Poseidon [Bariant et al. 2022] also apply to Poseidon2's structure; the paper discusses them
  [Grassi et al. 2023, §7.3].

## Assurance

The evidence that the Lean specification is the Poseidon2 of the paper and of each instance's
source, as of 2026-10-12:

| Evidence | Status |
|----------|--------|
| Reference transcription | `Hash.ZK.Poseidon2.Reference`, with the matrices as parameters, each definition citing its section of the paper; the instances cite HorizenLabs' and Plonky3's sources. |
| Constants | Round constants defined as the output of the Grain generator, in HorizenLabs' order; checked against the implementations by computation, not in the kernel. Plonky3's diagonals are transcribed from its source code (not from its comments). |
| Fast = reference | Proved in every commutative ring (`Hash.ZK.Poseidon2.Fast.permutation_eq`), for CompPoly's BabyBear, KoalaBear and BN254 fields (`HashZK.Poseidon2`), and for the raw fields of the C export (`HashZK.Raw.Poseidon2Equiv`). The axiom audit shows only `propext`, `Classical.choice` and `Quot.sound`. The byte encoding of the C export is not proved. |
| Known-answer tests | The authors' vectors pass: HorizenLabs' BN254 vector from `zkhash`, and Plonky3 0.8.0's default vectors for BabyBear and KoalaBear at widths 16 and 24, through the specification and through CompPoly (`lake exe hash-kat`). |
| Differential testing | Edge and random states agree with Plonky3 0.8.0 (scalar and SIMD code paths) for the 31-bit instances, and with `zkhash` and Plonky3's `p3-bn254` for BN254. |
| Fuzzing | One `cargo-fuzz` target over all five instances; no divergence has been found. The roadmap's budget of $10^9$ executions has not yet been reached. |
| Known deviations | Plonky3 is the only implementation of its BabyBear and KoalaBear instances (SP1's is a fork), so they are checked against one implementation, through two code paths. The width-4 external matrix ($M_4$ alone) and the width-32 instances are not covered. |

## In this directory

| File | Contents |
|------|----------|
| `Reference.lean` | `Params`; the matrices `onesPlusDiag`, `externalSmall`, `blockCirculant`; the reference specification `Reference.externalRound`, `Reference.internalRound`, `Reference.permutation`, over any commutative ring. |
| `Fast.lean` | The executable specification over the operations of `Hash.ZK.FieldOps`: `Fast.External`, `Fast.Params`, `sum`, `externalSmall`, `blockMul`, `externalM4`, `external`, `internal`, `externalRound`, `internalRound`, `permutation`; `Fast.map_permutation` (maps preserving the operations commute with it). Does not import Mathlib. |
| `Equiv.lean` | `Fast.Params.toRef` and the proofs that the fast layers are the matrices (`externalSmall_eq`, `externalM4_eq`, `internal_eq`) and that the fast permutation computes the reference (`permutation_eq`). |
| `InstanceParams.lean` | `grainSamples`; `Dyadic`, `plonky3M4` and the four Plonky3 diagonals; the `Plonky3` record and `babyBear16`, `babyBear24`, `koalaBear16`, `koalaBear24`; `Plonky3.fastParams`, `hlBn254Samples`, `hlBn254FastParams`. Does not import Mathlib. |
| `Instances.lean` | The instances over `ZMod p`: `Plonky3.params`, `Plonky3.permutation`, `hlBn254Params`, `hlBn254Permutation`; proofs that the fast parameters represent them. |
| `Sponge.lean` | `Plonky3.sponge` and `Plonky3.compress`, over any rate, output and chunk. |

**Shared pieces.** `Hash/ZK/Common/` holds what Poseidon2 shares with Poseidon: `Sbox.lean` (the
S-box and its inverse exponent), `Grain.lean` (the Grain LFSR), `Primes.lean` (`bn254`,
`babyBear`, `koalaBear`), `FieldOps.lean` (the `FieldOps` class and its maps `FieldOps.Hom`) and
`RingOps.lean` (`FieldOps` on any commutative ring). `Hash/Construction/FieldSponge.lean` defines
the field sponges, and `FieldSpongeLemmas.lean` proves `absorb_append` and that the sponges
commute with maps (`map_paddingFree`, `map_truncatedPermutation`, `map_onList`).

**Layer 2.** `zk/HashZK/Poseidon2.lean` runs the instances on CompPoly's Montgomery fields
(`BabyBear.Fast.Field`, `KoalaBear.Fast.Field`, and the BN254 scalar field) as
`HashZK.Poseidon2.babyBear16` … `hlBn254`. `zk/HashZK/Raw/Poseidon2.lean` runs them on raw field
representations, on states of natural numbers, together with the sponge and compression; these
are what the C exports of `zk/HashFFI/Poseidon2.lean` (`hs_poseidon2`, `hs_poseidon2_sponge`,
`hs_poseidon2_compress`) call. `zk/HashZK/Raw/Poseidon2Equiv.lean` proves them equal to the
specifications.

**Main theorems** (namespace `Hash.ZK.Poseidon2` unless stated):

| Theorem | Statement |
|---------|-----------|
| `Fast.externalSmall_eq`, `Fast.externalM4_eq`, `Fast.internal_eq` | The fast linear layers are the multiplications by `externalSmall t`, `blockCirculant M4` (for $t \equiv 0 \pmod 4$) and `onesPlusDiag v`. |
| `Fast.permutation_eq` | In any commutative ring with inverses, for parameters whose external layer is valid for the width (`Fast.External.Valid`): `Fast.permutation P s = Reference.permutation P.toRef s`. |
| `Fast.map_permutation` | A map `f` preserving the field operations (`FieldOps.Hom f`) commutes with the fast permutation. |
| `Plonky3.map_permutation_fastParams` | For a Plonky3 instance `I` with `I.t % 4 = 0` and any representation `F` related to `ZMod I.p` by a `FieldOps.Hom f`: `(Fast.permutation (I.fastParams F) s).map f = I.permutation (s.map f)`. |
| `map_permutation_hlBn254FastParams` | The same for HorizenLabs' BN254 instance and `hlBn254Permutation`. |
| `HashZK.Poseidon2.babyBear16_eq` … `koalaBear24_eq`, `HashZK.Poseidon2.hlBn254_eq` | Each CompPoly instance, mapped through CompPoly's ring isomorphism, is its specification. |
| `HashZK.Raw.Poseidon2.babyBear16_eq` … `hlBn254_eq` | Each raw instance, on natural numbers, is its specification on the inputs reduced modulo $p$. |
| `HashZK.Raw.Poseidon2.babyBear16_sponge_eq` … `koalaBear24_compress_eq` | The raw sponge and compression of each 31-bit instance are `Plonky3.sponge` and `Plonky3.compress`. |
| `Hash.FieldSponge.absorb_append` | (namespace `Hash`) Absorbing a block-aligned prefix and then the rest is absorbing everything. |

**Scope of the guarantees.**

- The proofs cover the permutation, sponge and compression on field elements. The byte encoding
  of the C exports (`zk/HashFFI/Poseidon2.lean`) is not proved; it is exercised by the differential
  tests and fuzzing in `harness/`.
- The round constants are definitions (the Grain output), not tables proved equal to published
  ones; agreement with the implementations rests on the known-answer and differential tests.
- Only the instances above are covered: not the width-4 external matrix, Plonky3's width-32
  instances, HorizenLabs' other instances, or Plonky3 releases before the KoalaBear fix.
- The theorems above are audited in `HashTests/Axioms.lean` and `zk/HashZKTests/Axioms.lean`.

## References

- **[Grassi et al. 2023]** L. Grassi, D. Khovratovich, M. Schofnegger. Poseidon2: A Faster Version of
  the Poseidon Hash Function. In *Progress in Cryptology – AFRICACRYPT 2023*, LNCS 14064,
  pp. 177–203, 2023. <https://doi.org/10.1007/978-3-031-37679-5_8>; full version ePrint 2023/323
  (revision of 2024-02-08), <https://eprint.iacr.org/2023/323>
- **[Grassi et al. 2021]** L. Grassi, D. Khovratovich, C. Rechberger, A. Roy, M. Schofnegger.
  Poseidon: A New Hash Function for Zero-Knowledge Proof Systems. In *30th USENIX Security
  Symposium*, 2021. <https://eprint.iacr.org/2019/458>
- **[Bariant et al. 2022]** A. Bariant, C. Bouvier, G. Leurent, L. Perrin. Algebraic Attacks
  against Some Arithmetization-Oriented Primitives. *IACR Transactions on Symmetric Cryptology*
  2022(3), pp. 73–101, 2022. <https://doi.org/10.46586/tosc.v2022.i3.73-101>
- **[HorizenLabs]** HorizenLabs. The Poseidon2 reference implementation and parameter script,
  commit 055bde3f, published as the `zkhash` crate. <https://github.com/HorizenLabs/poseidon2>
- **[Plonky3]** Plonky3 0.8.0. <https://github.com/Plonky3/Plonky3>
- The known-answer vectors, `zk/HashKAT/vectors/poseidon2/kats.json`, with their provenance in
  `zk/HashKAT/vectors/README.md`.
