/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import VersoManual
import Hash.ZK.Poseidon2.Instances
import HashDocs.Bibliography

/-!
# The Poseidon2 chapter of the book

The specification of Poseidon2 and of the HorizenLabs and Plonky3 instances, with a worked example
evaluated when the book is built.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open HashDocs.Bib

#doc (Manual) "Poseidon2" =>
%%%
tag := "poseidon2"
%%%

Poseidon2 is the permutation of *Poseidon2: A Faster Version of the Poseidon Hash Function* by
Lorenzo Grassi, Dmitry Khovratovich and Markus Schofnegger {citep grassi2023}[] (full version
[ePrint 2023/323](https://eprint.iacr.org/2023/323), revision of 2024-02-08). This chapter
explains the design alongside its Lean specification, `Hash.ZK.Poseidon2`, and the instances of
HorizenLabs' reference implementation and of Plonky3. Section numbers in parentheses refer to the
ePrint version.

# Overview and history
%%%
tag := "poseidon2-overview"
%%%

Poseidon2 keeps Poseidon's HADES structure: full rounds at each end and partial rounds in the
middle. It changes the linear layers so that they cost `O(t)` operations instead of `O(t²)`. The
full rounds, now called *external*, multiply by a matrix built from a fixed 4×4 MDS matrix. The
partial rounds, now called *internal*, multiply by a matrix that is all ones except for its
diagonal. Two more changes: the permutation starts with a multiplication by the external matrix
(§4), and an internal round adds a constant to the first element only (§6).

Poseidon2 is used in STARK systems over 31-bit fields: Plonky3 and the systems built on it (SP1,
OpenVM), and RISC Zero. It is also used over BN254, for example in Noir's standard library. As
with Poseidon, implementations differ in their matrices and constants, so "Poseidon2" names a
family, and each instance here is named after its source.

:::table +header
*
  * Instance
  * Field
  * `t`
  * `d`
  * `R_F`, `R_P`
  * External `M₄`
*
  * HorizenLabs BN254
  * BN254 scalar field
  * 3
  * 5
  * 8, 56
  * none: `circ(2, 1, 1)`
*
  * Plonky3 BabyBear
  * $`2^{31} - 2^{27} + 1`
  * 16, 24
  * 7
  * 8, 13 / 21
  * `circ(2, 3, 1, 1)`
*
  * Plonky3 KoalaBear
  * $`2^{31} - 2^{24} + 1`
  * 16, 24
  * 3
  * 8, 20 / 23
  * `circ(2, 3, 1, 1)`
:::

# The permutation
%%%
tag := "poseidon2-permutation"
%%%

The state is a vector of `t` field elements. The permutation multiplies by `M_E`, applies
`R_F / 2` external rounds, then `R_P` internal rounds, then `R_F / 2` external rounds (§6):

{docstring Hash.ZK.Poseidon2.Params}

{docstring Hash.ZK.Poseidon2.Reference.externalRound}

{docstring Hash.ZK.Poseidon2.Reference.internalRound}

{docstring Hash.ZK.Poseidon2.Reference.permutation}

# The linear layers
%%%
tag := "poseidon2-linear"
%%%

For widths that are multiples of 4, the external matrix is `circ(2·M₄, M₄, …, M₄)`: the state
splits into blocks of four, and block `(a, b)` of the matrix is `2·M₄` on the diagonal and `M₄`
elsewhere (§5.1). The paper's `M₄` is `[[5,7,1,3],[4,6,1,1],[1,3,5,7],[1,1,4,6]]`; Plonky3's
31-bit instances use `circ(2, 3, 1, 1)` instead. For widths 2 and 3 the implementations take
`circ(2, 1)` and `circ(2, 1, 1)`, while the paper's text sets `M_E = M_I` (§6). The specification
follows the implementations.

{docstring Hash.ZK.Poseidon2.blockCirculant}

{docstring Hash.ZK.Poseidon2.externalSmall}

The internal matrix is `J + diag(v)`, where `J` is all ones (§5.2). Multiplying by it costs one
sum and `t` multiplications: `y_i = v_i · x_i + Σ_j x_j`. Plonky3 picks the entries `v_i` among
small powers of 2 and their negatives and inverses, so that each multiplication is a shift.

{docstring Hash.ZK.Poseidon2.onesPlusDiag}

The fast specification computes the layers this way. The library proves that the results are
the matrix products, including the block-reindexing argument for `circ(2·M₄, M₄, …)`:

{docstring Hash.ZK.Poseidon2.Fast.externalM4_eq}

{docstring Hash.ZK.Poseidon2.Fast.permutation_eq}

# Parameters and constants
%%%
tag := "poseidon2-constants"
%%%

The round constants come from the Grain LFSR of the Poseidon chapter, seeded with the field
size, the width and the round numbers. The paper says only that they are "generated as in
Poseidon" (§6); the order comes from HorizenLabs' generation script. That order is the initial
external constants, then the internal constants, then the final external constants:

{docstring Hash.ZK.Poseidon2.grainSamples}

{docstring Hash.ZK.Poseidon2.Plonky3.params}

{docstring Hash.ZK.Poseidon2.hlBn254ParamsOf}

Plonky3 releases before 0.6 drew the KoalaBear constants in a different order (initial, final,
internal). Those releases compute a different permutation under the same name. This library
follows the corrected order, which Plonky3 0.8.0 ships.

# Worked example
%%%
tag := "poseidon2-example"
%%%

We compute HorizenLabs' BN254 instance on the state `[0, 1, 2]`. The values are computed when
this book is built, and the build fails if any differs from the text shown.

```lean
open Hash.ZK Hash.ZK.Poseidon2

/-- A field element in hexadecimal. -/
def p2Hex (x : ZMod bn254) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 x.val)
```

```lean (name := p2Bn254)
#eval do
  let s : Vector (ZMod bn254) 3 := #v[0, 1, 2]
  let P := hlBn254FastParams (ZMod bn254)
  let out := Fast.permutation P s
  for x in out.toList do IO.println (p2Hex x)
```

```leanOutput p2Bn254
0xbb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033
0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570
0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8
```

This is the vector of HorizenLabs' reference implementation. The fast permutation over `ZMod p`
is proved equal to the specification, so this is also the specification's output.

# Assurance status
%%%
tag := "poseidon2-assurance"
%%%

The evidence that the Lean specification is the Poseidon2 of the paper and of each instance's
source, as of 2026-10-12:

:::table +header
*
  * Evidence
  * Status
*
  * Reference transcription
  * `Hash.ZK.Poseidon2.Reference`, with the matrices as parameters, each definition citing its
    section of the paper; the instances cite HorizenLabs' and Plonky3's sources.
*
  * Constants
  * Round constants defined as the output of the Grain generator, in HorizenLabs' order; checked
    against the implementations by computation, not in the kernel. Plonky3's diagonals are
    transcribed from its source code (not from its comments).
*
  * Fast = reference
  * Proved in every commutative ring (`Hash.ZK.Poseidon2.Fast.permutation_eq`), for CompPoly's
    BabyBear, KoalaBear and BN254 fields (`HashZK.Poseidon2`), and for the raw fields of the C
    export (`HashZK.Raw.Poseidon2Equiv`). The axiom audit shows only `propext`,
    `Classical.choice` and `Quot.sound`. The byte encoding of the C export is not proved.
*
  * Known-answer tests
  * The authors' vectors pass: HorizenLabs' BN254 vector from `zkhash`, and Plonky3 0.8.0's
    default vectors for BabyBear and KoalaBear at widths 16 and 24, through the specification
    and through CompPoly (`lake exe hash-kat`).
*
  * Differential testing
  * Edge and random states agree with Plonky3 0.8.0 (scalar and SIMD code paths) for the 31-bit
    instances, and with `zkhash` and Plonky3's `p3-bn254` for BN254.
*
  * Fuzzing
  * One `cargo-fuzz` target over all five instances; no divergence has been found. The
    roadmap's budget of $`10^9` executions has not yet been reached.
*
  * Known deviations
  * Plonky3 is the only implementation of its BabyBear and KoalaBear instances (SP1's is a
    fork), so they are checked against one implementation, through two code paths. The width-4
    external matrix (`M₄` alone) and the width-32 instances are not covered.
:::

# Security notes
%%%
tag := "poseidon2-security"
%%%

This section points to the literature; it makes no claims of its own.

- *Round numbers.* Poseidon2 keeps Poseidon's round numbers. The paper argues that the new
  linear layers give the same security against statistical and algebraic attacks (§7). The
  initial multiplication by `M_E` is there because, otherwise, the first round's linear layer
  could be peeled off: a permutation used in a sponge should start and end with a linear layer
  (§4).
- *Internal matrix.* The diagonal must be chosen so that no subspace trail passes through
  arbitrarily many internal rounds. The paper gives a sufficient condition on the minimal
  polynomials of `M_I` and its powers (§5.3). Plonky3 documents its check of this condition for
  its hand-picked diagonals.
- *Cryptanalysis.* The attacks of Bariant, Bouvier, Leurent and Perrin on round-reduced Poseidon
  {citep bariant2022}[] also apply to Poseidon2's structure; the paper discusses them (§7.3).

# References
%%%
tag := "poseidon2-references"
%%%

- L. Grassi, D. Khovratovich and M. Schofnegger, *Poseidon2: A Faster Version of the Poseidon
  Hash Function*, AFRICACRYPT 2023; [ePrint 2023/323](https://eprint.iacr.org/2023/323).
- HorizenLabs, the Poseidon2 reference implementation and parameter script,
  [github.com/HorizenLabs/poseidon2](https://github.com/HorizenLabs/poseidon2), published as the
  `zkhash` crate.
- Plonky3 0.8.0, [github.com/Plonky3/Plonky3](https://github.com/Plonky3/Plonky3).
- The known-answer vectors, `HashKAT/vectors/poseidon2/kats.json`, with their provenance in
  `HashKAT/vectors/README.md`.

The papers cited in this chapter are listed in the book's bibliography.
