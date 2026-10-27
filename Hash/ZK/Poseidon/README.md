# Poseidon

Poseidon is the permutation and hash function of *Poseidon: A New Hash Function for
Zero-Knowledge Proof Systems* by Grassi, Khovratovich, Rechberger, Roy and Schofnegger
[Grassi et al. 2021]. It works on elements of a prime field $\mathbb{F}_p$ rather than on bits:
its round function uses only additions, multiplications and a low-degree power map, so a proof
system whose statements are equations over $\mathbb{F}_p$ (a SNARK or STARK circuit) can check one
evaluation with a few hundred constraints, where SHA-256 needs tens of thousands. Poseidon is not
standardised; implementations differ in their parameters and in how they hash, so "Poseidon" names
a family. This directory specifies the permutation for any parameters, and the instances of
iden3's circomlib [circomlib] over the BN254 scalar field, for one to sixteen inputs. These are
the instances used by Tornado Cash, Semaphore, Polygon ID and many circuits written in Circom, and
they also appear in go-iden3-crypto, light-poseidon and poseidon-rs. It contains a reference
specification over any commutative ring, an executable specification written over a small class
of field operations, a derivation of circomlib's constants from the Grain LFSR, and proofs that
the executable specification computes the reference in every representation of the field used
here. Section numbers such as §2.2 refer to the full version of the paper (ePrint 2019/458).

## Notation

- $\mathbb{F}_p$ is a prime field; the reference specification works in any commutative ring
  `F`, in practice `ZMod p`. For circomlib, $p$ is the BN254 scalar field order `bn254`
  ($\approx 2^{253.6}$, a 254-bit prime).
- The *state* is a vector $s = (s_0, \dots, s_{t-1})$ of $t$ field elements, the *width*. In Lean
  it is a `Vector F t`.
- $x \mapsto x^\alpha$ is the S-box (`Hash.ZK.sbox`).
- $c_r \in \mathbb{F}_p^t$ are the round constants of round $r$; $c_{r,i}$ is added to element
  $i$.
- $M$ is the $t \times t$ linear layer. The state is multiplied as a column vector:
  $s'_i = \sum_j M_{i,j} s_j$.
- **Indexing.** Round constants are numbered round-major: constant $r \cdot t + i$ of the flat
  list is $c_{r,i}$. Field elements cross the C boundary as 32-byte big-endian integers.

## Parameters

A Poseidon permutation is given by `Params F t` [Grassi et al. 2021, §2.2–2.3]:

| Field | Meaning |
|-------|---------|
| `α`   | The S-box exponent. |
| `RF`  | The number of full rounds $R_F$, half before and half after the partial rounds. |
| `RP`  | The number of partial rounds $R_P$. |
| `C`   | The round constants, `C r i` $= c_{r,i}$ for $r < R_F + R_P$. |
| `M`   | The matrix, a Mathlib `Matrix (Fin t) (Fin t) F`. |

**circomlib's instances** (`Hash.ZK.Poseidon.Circom.params`) have widths $t = 2, \dots, 17$
(one to sixteen inputs), $\alpha = 5$, $R_F = 8$, and $R_P$ from `partialRounds`: the output of the
reference round-number script for 128-bit security, rounded up to a multiple of $t$
[circomlib, `N_ROUNDS_P`]. Each instance has $(R_F + R_P) \cdot t$ round constants and a $t \times t$
matrix.

| $t$ | Inputs | $R_P$ | Constants | | $t$ | Inputs | $R_P$ | Constants |
|-----|--------|-------|-----------|-|-----|--------|-------|-----------|
| 2   | 1      | 56    | 128       | | 10  | 9      | 60    | 680       |
| 3   | 2      | 57    | 195       | | 11  | 10     | 66    | 814       |
| 4   | 3      | 56    | 256       | | 12  | 11     | 60    | 816       |
| 5   | 4      | 60    | 340       | | 13  | 12     | 65    | 949       |
| 6   | 5      | 60    | 408       | | 14  | 13     | 70    | 1092      |
| 7   | 6      | 63    | 497       | | 15  | 14     | 60    | 1020      |
| 8   | 7      | 64    | 576       | | 16  | 15     | 64    | 1152      |
| 9   | 8      | 63    | 639       | | 17  | 16     | 68    | 1292      |

For BN254, $\alpha = 5$ is the smallest exponent with $\gcd(\alpha, p - 1) = 1$ [Grassi et al. 2021, §2.3].

## The permutation

Poseidon is an instance of the HADES strategy: $R_F / 2$ *full* rounds, with an S-box on every
element, then $R_P$ cheaper *partial* rounds, with one S-box, then $R_F / 2$ full rounds
[Grassi et al. 2021, §2.2]. Round $r$ is full when $r < R_F/2$ or $R_F/2 + R_P \le r$
(`Reference.isFull`). Every round, including the last, is

$$\mathrm{ARC}: s_i \leftarrow s_i + c_{r,i}, \qquad
\mathrm{SB}: s_i \leftarrow \begin{cases} s_i^\alpha & \text{full round, or } i = 0, \\ s_i & \text{otherwise,} \end{cases}
\qquad \mathrm{M}: s \leftarrow M s,$$

in this order (`Reference.sboxLayer`, `Reference.round`). The permutation is the left fold of
`round` over $r = 0, \dots, R_F + R_P - 1$ (`Reference.permutation`).

**The S-box** [Grassi et al. 2021, §2.3]. The power map $x \mapsto x^\alpha$ is a permutation of a
finite field $\mathbb{F}_q$ exactly when $\gcd(\alpha, q - 1) = 1$. The library proves the "if"
direction (`Hash.ZK.sbox_bijective`), and that $x \mapsto x^{\beta}$ with
$\beta = \alpha^{-1} \bmod (q - 1)$ (`Hash.ZK.invExponent`) inverts it
(`Hash.ZK.sbox_sbox_invExponent`, `Hash.ZK.sbox_invExponent_sbox`).

**The fast permutation** (`Hash.ZK.Poseidon.Fast`) holds the round constants in one `Array`
(constant $r \cdot t + i$ for element $i$ of round $r$) and the matrix as a vector of rows, and
computes each matrix row as a dot product. It is written over `Hash.ZK.FieldOps`, a class with
`zero`, `one`, `add`, `neg`, `mul`, `ofNat` and `inv`, with powers by square-and-multiply
(`FieldOps.pow`), so that the same code runs on three representations of $\mathbb{F}_p$:

- `ZMod p`, and any commutative ring with an inverse (`FieldOps.ofCommRing`), where it is proved to
  compute the reference (`Fast.permutation_eq`);
- CompPoly's eight-limb Montgomery field `BN254.Fast.ScalarField` (`HashZK.Poseidon.Circom`);
- the raw limbs of that representation, without the proof that they are reduced (`HashZK.Raw`),
  whose import closure is free of Mathlib so that the C exports of `HashFFI` can link it.

A map between representations that preserves the operations (`FieldOps.Hom`) commutes with the
permutation (`Fast.map_permutation`) and with the parameter derivation
(`Circom.map_fastParams`). CompPoly's ring isomorphism with `ZMod p`, and the map from its
elements to their limbs, are such maps, so each representation computes the specification.

## Constants

Poseidon's round constants are pseudorandom field elements, and its matrix is a Cauchy matrix
$M_{i,j} = 1 / (x_i + y_j)$, which is MDS. Both are drawn from an 80-bit Grain LFSR in
self-shrinking mode [Grassi et al. 2021, App. E; hadeshash]. Implementations usually ship the
outputs as tables. This library instead defines the constants as the output of the generator
(`Hash.ZK.Grain`), so a reader can check the derivation rather than trust a table.

**Initial state** (`Grain.init`). The bits $b_0, \dots, b_{79}$ are, most significant bit first:
the field type (2 bits; 1 for $\mathbb{F}_p$), the S-box code (4 bits), the field size $n$ (12
bits), $t$ (12 bits), $R_F$ (10 bits), $R_P$ (10 bits), and thirty ones. In Lean the state is a
natural number below $2^{80}$ whose most significant bit is $b_0$. circomlib's instances use
`grainParams t` $= (1, 0, 254, t, 8, R_P)$, as the reference script invoked as
`sage generate_parameters_grain.sage 1 0 254 t 8 R_P p`. The reference script (and circomlib)
encode $x^\alpha$ as S-box code 0; Filecoin's Neptune uses 1 for $x^5$, which gives different
constants for the "same" parameters, so the code is a parameter.

**Clocking** (`Grain.clock`). Each clock outputs
$b_{i+80} = b_{i+62} \oplus b_{i+51} \oplus b_{i+38} \oplus b_{i+23} \oplus b_{i+13} \oplus b_i$.
The first 160 outputs are discarded. Output bits are then taken in pairs; if the first is 1 the
second is output, otherwise both are discarded (`Grain.nextBit`).

**Sampling.** A field element is $n$ output bits read most significant first:

- the $(R_F + R_P) \cdot t$ round constants are each sampled again while not below $p$
  (`Grain.sampleBelow`, `Grain.sampleList`);
- then, from the same stream, $2t$ further $n$-bit numbers are reduced modulo $p$ (no
  rejection, `Grain.rawList`) to give $x_0, \dots, x_{t-1}, y_0, \dots, y_{t-1}$; all $2t$ are
  drawn again until they are distinct and no $x_i + y_j$ is zero (`Circom.cauchySeeds`).

`Circom.samples` returns both lists. Loops carry fuel (`nextBit` 1000 discarded pairs,
`sampleBelow` 1000 rejections, `cauchySeeds` 100 redraws) so that the definitions are total; no
circomlib instance comes near these bounds, since its constants match the published tables.

The reference script also checks each matrix for infinitely long subspace trails and samples again
on failure [Grassi et al. 2021, §2.3]. The specification does not repeat the check: the first sample
passes for every circomlib width, which the agreement with circomlib's matrices confirms.

The kernel cannot evaluate the generator for these instances: each 254-bit constant takes
thousands of LFSR clocks. The constants are therefore not *proved* equal to circomlib's tables;
they agree with them by computation, and the known-answer and differential tests would fail on any
wrong constant.

## Hashing

circomlib hashes $n$ inputs with one application of the width-$(n + 1)$ permutation to the state
$[0, x_1, \dots, x_n]$, and outputs the first element (`Circom.poseidon`). `PoseidonEx`
generalises the initial first element (`initState`) and the number of outputs `nOut`, taking the
first `nOut` elements of the permuted state (`Circom.poseidonEx`). There is no sponge, padding or
domain separation, unlike the sponge of [Grassi et al. 2021, §2.1, §4.2]; different input counts use
different widths, and the output is the capacity element rather than a rate element.

**Worked example.** circomlib's `Poseidon(2)` on the inputs `1` and `2` uses the width-3
instance, $R_F = 8$, $R_P = 57$, so 195 round constants. The first round constant, the first
matrix entry, and the hash are

```
c_{0,0} = 0xee9a592ba9a9518d05986d656f40c2114c4993c11bb29938d21d47304cd8e6e
M_{0,0} = 0x109b7f411ba0e4c9b2b70caf5c36a7b194be7c11ad24378bfedb68592ba8118b
Poseidon(1, 2) = 0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a
```

The first two are the first entries of circomlib's tables `C` and `M` for $t = 3$; the last is
the value in circomlib's test suite.

## Security notes

This section points to the literature; this directory proves no security property.

- **Round numbers.** The paper chooses $R_F$ and $R_P$ from statistical (differential, linear)
  and algebraic (interpolation, Gröbner basis) attacks, adds a security margin of two full rounds
  and 7.5% of the partial rounds, and circomlib rounds $R_P$ up further
  [Grassi et al. 2021, §4.1, §5].
- **Matrix.** Some Cauchy matrices let invariant subspaces pass through all partial rounds; the
  reference script tests for these "infinitely long subspace trails" and rejects such matrices
  [Grassi et al. 2021, §2.3; Grassi et al. 2020].
- **Cryptanalysis.** Bariant, Bouvier, Leurent and Perrin solve round-reduced CICO problems for
  Poseidon with algebraic attacks, in response to the Ethereum Foundation's bounties
  [Bariant et al. 2022]. Their attacks do not reach the full round numbers.
- **Use as a hash.** circomlib's construction is a fixed-length compression of up to 16 elements.
  It is not a sponge, and it is collision resistant only for inputs of one fixed length.

## Assurance

The evidence that the Lean specification is circomlib's Poseidon, as of 2026-10-12:

| Evidence | Status |
|----------|--------|
| Reference transcription | `Hash.ZK.Poseidon.Reference`, `Hash.ZK.Grain` and `Hash.ZK.Poseidon.Circom`, each definition citing its section of the paper, the reference script or circomlib. |
| Constants | Defined as the output of the Grain generator, as circomlib's were; checked against circomlib's tables by computation (the known-answer and differential tests), not proved in the kernel, which cannot evaluate the generator at this size. |
| Fast = reference | Proved in every commutative ring (`Hash.ZK.Poseidon.Fast.permutation_eq`), for CompPoly's Montgomery field (`HashZK.Poseidon.Circom.poseidon_eq`) and for the raw limbs of the C export (`HashZK.Raw.Poseidon.poseidonNat_eq`). The axiom audit shows only `propext`, `Classical.choice` and `Quot.sound`. The 32-byte encoding of the C export is not proved. |
| Streaming | Not applicable: circomlib's Poseidon hashes a fixed number of field elements. |
| Known-answer tests | 36 vectors for widths 2–13, 15 and 17, from go-iden3-crypto, light-poseidon and the reference implementation, pass through the specification over `ZMod p` and through CompPoly's field (`lake exe hash-kat`). No upstream test covers widths 14 and 16; the differential tests do. |
| Differential testing | Every width, edge values ($0$, $p - 1$, $p$, $2^{256} - 1$) and random inputs agree with `poseidon-rs` (all widths) and `light-poseidon` (up to 12 inputs). |
| Fuzzing | One `cargo-fuzz` target against both oracles; no divergence has been found. The roadmap's budget of $10^9$ executions has not yet been reached. |
| Other formal specifications | Informational, from `LIT-REVIEW.md`: Lean specifications in Clean (circomlib's BN254 instance, arity 1) and Reilabs' gnark extractor (BN254, $t = 2, 3$), ACL2 (Kestrel/Provable), and Rocq (Formal Land's Garden, Zcash Orchard's Pallas instance). |
| Known deviations | The reference script checks each matrix for infinitely long subspace trails and samples again on failure; the specification does not repeat the check. The first sample passes for every circomlib width, which the agreement with circomlib's matrices confirms. The C export reduces inputs modulo $p$, as the Rust oracles do; circomlib's circuits take field elements. |

## In this directory

| File | Contents |
|------|----------|
| `Reference.lean` | `Params` and the reference specification `Reference.*`: `isFull`, `sboxLayer`, `round`, `permutation`, over any commutative ring with the matrix a Mathlib `Matrix`; `Params.map` and the proof that ring homomorphisms commute with the permutation. |
| `Fast.lean` | The executable specification over `Hash.ZK.FieldOps`: `Fast.Params` (constants in an `Array`, matrix as rows), `dot`, `round`, `permutation`; `Fast.Params.map` and the proof that maps preserving the operations commute with the permutation. Does not import Mathlib. |
| `Equiv.lean` | `Fast.Params.toRef` and the proof that the fast permutation computes the reference in every commutative ring with an inverse. |
| `CircomParams.lean` | circomlib's `partialRounds`, `grainParams`, `cauchySeeds`, `samples`, and `fastParams` in any representation of the field; `map_fastParams`. Does not import Mathlib, so that the C exports can use it. |
| `Circom.lean` | The instances over `ZMod bn254`: `params`, `poseidonEx`, `poseidon`; `fastParams_toRef` and `map_permutation_fastParams`. |

**Shared pieces.** `Hash/ZK/Common/` holds what Poseidon shares with the other ZK-friendly hashes:
`Sbox.lean` (`sbox`, `invExponent` and the bijectivity proofs), `Grain.lean` (the Grain LFSR),
`FieldOps.lean` (the operation class, `pow`, `FieldOps.Hom`), `RingOps.lean` (the instance for
commutative rings, `FieldOps.pow_eq`, `FieldOps.Hom.ofRingHom`) and `Primes.lean` (`bn254` and
the other moduli). `Hash/Construction/FieldSponge.lean` and `FieldSpongeLemmas.lean` define the
field sponges and compressions (Plonky3's `paddingFree` and `truncatedPermutation`) used by
Poseidon2; circomlib's Poseidon does not use them, and that file names `Circom.poseidonEx` as
circomlib's one-shot hash.

**Layer 2** (CompPoly-backed, outside `Hash/`):

| File | Contents |
|------|----------|
| `HashZK/Poseidon/Circom.lean` | circomlib's Poseidon over `BN254.Fast.ScalarField` (`Fr`), with the parameters of each width derived once on first use (`paramsCache`); `poseidonEx`, `poseidon`; `permutation_eq`, `poseidon_eq` through the ring isomorphism `toZMod`. |
| `HashZK/Raw/BN254.lean` | The BN254 scalar field on raw Montgomery limbs (`Fr`, `toNat`, `ofNat`), with inverse $x^{p-2}$; no Mathlib in its import closure. |
| `HashZK/Raw/Poseidon.lean` | circomlib's Poseidon on raw limbs: `paramsCache`, `initState`, `poseidon`, and `poseidonNat` on natural numbers (inputs reduced modulo $p$). |
| `HashZK/Raw/Equiv.lean` | `toRaw`, `hom_toRaw`, `toNat_toRaw` and `poseidonNat_eq`. |

The C entry point `hs_poseidon_circom` (`HashFFI/Poseidon.lean`) takes one to sixteen 32-byte
big-endian integers and calls `HashZK.Raw.Poseidon.poseidonNat`.

**Main theorems** (namespace `Hash.ZK` unless stated):

| Theorem | Statement |
|---------|-----------|
| `sbox_bijective` | $x \mapsto x^\alpha$ is a bijection of a finite field $\mathbb{F}_q$, $q > 2$, when $\gcd(\alpha, q - 1) = 1$. |
| `sbox_sbox_invExponent`, `sbox_invExponent_sbox` | $x \mapsto x^{\beta}$, $\beta$ = `invExponent α q`, is a two-sided inverse of the S-box. |
| `Poseidon.Reference.map_permutation` | A ring homomorphism $\varphi$ commutes with the permutation: `(permutation P s).map φ = permutation (P.map φ) (s.map φ)`. |
| `Poseidon.Fast.permutation_eq` | In a commutative ring with an inverse, `Fast.permutation P s = Reference.permutation P.toRef s`; `Poseidon.Fast.round_eq` is the per-round lemma. |
| `Poseidon.Fast.map_permutation` | A map preserving the `FieldOps` operations commutes with the fast permutation. |
| `FieldOps.pow_eq`, `FieldOps.Hom.ofRingHom` | In a commutative ring, square-and-multiply computes `x ^ n`; ring homomorphisms preserving inverses preserve the operations. |
| `Poseidon.Circom.fastParams_toRef`, `Poseidon.Circom.map_fastParams` | Over `ZMod bn254` the fast parameters represent `params t`; maps preserving the operations carry the fast parameters of one representation to another. |
| `Poseidon.Circom.map_permutation_fastParams` | For any representation `F` and map `f : F → ZMod bn254` preserving the operations, the fast permutation with `fastParams F t`, mapped by `f`, is `Reference.permutation (params t)`. |
| `HashZK.Poseidon.Circom.permutation_eq`, `HashZK.Poseidon.Circom.poseidon_eq` | The same over CompPoly's `Fr`: `toZMod (poseidon inputs) = Hash.ZK.Poseidon.Circom.poseidon inputs.size (toZMod inputs[·])`. |
| `HashZK.Raw.Poseidon.poseidonNat_eq` | `poseidonNat inputs` is the value of `Hash.ZK.Poseidon.Circom.poseidon` on the inputs cast to `ZMod bn254`. |

**Scope of the guarantees.**

- The theorems relate the executable code to the reference permutation with the derived
  parameters. That the derived constants are circomlib's is established by the tests, not by a
  proof; so is the absence of subspace trails in the derived matrices.
- `partialRounds` is defined only for $t = 2, \dots, 17$ (it returns 0 otherwise), so
  `Circom.poseidon n` is circomlib's only for $n = 1, \dots, 16$.
- The byte encoding of the C export (`HashFFI.poseidonCircom`) is not proved; the harness tests it.
- The theorems above are audited in `HashTests/Axioms.lean` and `HashZKTests/Axioms.lean`.

## References

- **[Grassi et al. 2021]** L. Grassi, D. Khovratovich, C. Rechberger, A. Roy, M. Schofnegger.
  Poseidon: A New Hash Function for Zero-Knowledge Proof Systems. In *30th USENIX Security
  Symposium*, pp. 519–535, 2021. Full version: ePrint 2019/458. <https://eprint.iacr.org/2019/458>
- **[Grassi et al. 2020]** L. Grassi, C. Rechberger, M. Schofnegger. Proving Resistance Against
  Infinitely Long Subspace Trails: How to Choose the Linear Layer. *IACR Transactions on Symmetric
  Cryptology* 2021(2), 2021. <https://eprint.iacr.org/2020/500>
- **[Bariant et al. 2022]** A. Bariant, C. Bouvier, G. Leurent, L. Perrin. Algebraic Attacks against
  Some Arithmetization-Oriented Primitives. *IACR Transactions on Symmetric Cryptology* 2022(3),
  pp. 73–101, 2022. <https://doi.org/10.46586/tosc.v2022.i3.73-101>
- **[hadeshash]** The Poseidon reference implementation, `code/generate_parameters_grain.sage`,
  commit 208b5a16. <https://extgit.iaik.tugraz.at/krypto/hadeshash>
- **[circomlib]** iden3, `circuits/poseidon.circom` and `circomlibjs/src/poseidon_reference.js`,
  commits 35e54ea2 and 48b3ab37. <https://github.com/iden3/circomlib>
- **[KAT]** The known-answer vectors, `HashKAT/vectors/poseidon/circomlib-bn254.json`, with their
  provenance in `HashKAT/vectors/README.md`.
