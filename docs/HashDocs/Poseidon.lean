/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import VersoManual
import Hash.ZK.Poseidon.Circom
import HashDocs.Bibliography

/-!
# The Poseidon chapter of the book

The specification of Poseidon and circomlib's BN254 instances, with a worked example evaluated
when the book is built.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open HashDocs.Bib

#doc (Manual) "Poseidon" =>
%%%
tag := "poseidon"
%%%

Poseidon is the permutation and hash function of *Poseidon: A New Hash Function for
Zero-Knowledge Proof Systems* by Lorenzo Grassi, Dmitry Khovratovich, Christian Rechberger,
Arnab Roy and Markus Schofnegger {citep grassi2021}[] (full version
[ePrint 2019/458](https://eprint.iacr.org/2019/458)). This chapter explains the design alongside
its Lean specification, `Hash.ZK.Poseidon`, and the instances of iden3's circomlib over the BN254
scalar field. Section numbers in parentheses refer to the full version.

# Overview and history
%%%
tag := "poseidon-overview"
%%%

Poseidon works on elements of a prime field $`\mathbb{F}_p` rather than on bits. Its round
function uses only additions, multiplications and a low-degree power map, so a proof system
whose statements are equations over $`\mathbb{F}_p` (a SNARK or STARK circuit) can check one
evaluation with a few hundred constraints, where SHA-256 needs tens of thousands. Poseidon is
an instance of the HADES strategy: a few *full* rounds, with an S-box on every element, at
each end, around many cheaper *partial* rounds, with one S-box (§2.2).

Poseidon is not standardised. Implementations differ in their parameters and in how they hash,
so "Poseidon" names a family. This library specifies the permutation for any parameters, and
the instances of circomlib, which Tornado Cash, Semaphore, Polygon ID and many circuits written
in Circom use. They also appear in go-iden3-crypto, light-poseidon and poseidon-rs.

The *reference* specification (`Hash.ZK.Poseidon.Reference`) works in any commutative ring, with
the state a vector and the matrix a Mathlib `Matrix`. The *fast* specification
(`Hash.ZK.Poseidon.Fast`) holds the constants in an array and the matrix as vectors of rows. It
is written over a small class of field operations, `Hash.ZK.FieldOps`, so that the same code
runs on `ZMod p`, on CompPoly's Montgomery field, and on raw limbs for the C exports.

# The round function
%%%
tag := "poseidon-round"
%%%

The state is a vector of `t` field elements. Round `r` adds the round constants (`ARC`), applies
the S-box (`SB`) to every element in a full round and to the first element in a partial round,
and multiplies by a `t × t` matrix (`M`). There are `R_F` full rounds, half before and half
after the `R_P` partial rounds (§2.2).

{docstring Hash.ZK.Poseidon.Params}

{docstring Hash.ZK.Poseidon.Reference.isFull}

{docstring Hash.ZK.Poseidon.Reference.sboxLayer}

{docstring Hash.ZK.Poseidon.Reference.round}

{docstring Hash.ZK.Poseidon.Reference.permutation}

The S-box is the power map $`x \mapsto x^\alpha`. It is a permutation of $`\mathbb{F}_q` exactly
when $`\gcd(\alpha, q - 1) = 1`; the library proves the "if" direction, and that
$`x \mapsto x^{\alpha^{-1} \bmod (q-1)}` inverts it. For BN254, $`\alpha = 5` is the smallest
such exponent (§2.3).

{docstring Hash.ZK.sbox}

{docstring Hash.ZK.sbox_bijective}

# Parameters and constants
%%%
tag := "poseidon-constants"
%%%

Poseidon's round constants are pseudorandom field elements, and its matrix is an MDS Cauchy
matrix $`M_{i,j} = 1 / (x_i + y_j)`. Both are drawn from an 80-bit Grain LFSR seeded with the
field, the S-box, the width and the round numbers (App. E). Implementations usually ship the
outputs as tables. This library instead defines the constants as the output of the generator,
so a reader can check the derivation rather than trust a table.

{docstring Hash.ZK.Grain.init}

{docstring Hash.ZK.Grain.nextBit}

{docstring Hash.ZK.Grain.sampleBelow}

circomlib's instances have widths `t = 2 … 17` (one to sixteen inputs), $`\alpha = 5`,
`R_F = 8`, and partial round numbers from the reference script, rounded up for 128-bit security:

{docstring Hash.ZK.Poseidon.Circom.partialRounds}

{docstring Hash.ZK.Poseidon.Circom.cauchySeeds}

{docstring Hash.ZK.Poseidon.Circom.params}

The kernel cannot evaluate the generator for these instances: each 254-bit constant takes
thousands of LFSR clocks. The constants are therefore not *proved* equal to circomlib's tables.
They agree with them by computation: the known-answer tests and the differential tests below
would fail on any wrong constant.

# Hashing
%%%
tag := "poseidon-hash"
%%%

circomlib hashes `n` inputs with one application of the width-`n + 1` permutation to the state
`[0, x₁, …, x_n]`, and outputs the first element. There is no sponge, padding or domain
separation; different input counts use different widths. `PoseidonEx` generalises the initial
first element and the number of outputs.

{docstring Hash.ZK.Poseidon.Circom.poseidon}

{docstring Hash.ZK.Poseidon.Circom.poseidonEx}

# Representations of the field
%%%
tag := "poseidon-representations"
%%%

The fast permutation is written once, over `Hash.ZK.FieldOps`, and run in three representations
of $`\mathbb{F}_p`:

- `ZMod p` and other commutative rings with inverses, where it is proved to compute the
  reference (`Hash.ZK.Poseidon.Fast.permutation_eq`);
- CompPoly's eight-limb Montgomery field `BN254.Fast.ScalarField` (`HashZK.Poseidon.Circom`);
- the raw limbs of that representation, without the proof that they are reduced
  (`HashZK.Raw`), whose import closure is free of Mathlib so that the C exports can link it.

A map between representations that preserves the operations commutes with the permutation
(`Hash.ZK.Poseidon.Fast.map_permutation`) and with the parameter derivation
(`Hash.ZK.Poseidon.Circom.map_fastParams`). CompPoly's ring isomorphism with `ZMod p`, and the
map from its elements to their limbs, are such maps. So each representation computes the
specification:

{docstring Hash.ZK.Poseidon.Fast.permutation_eq}

{docstring Hash.ZK.Poseidon.Fast.map_permutation}

# Worked example
%%%
tag := "poseidon-example"
%%%

We compute circomlib's `Poseidon(2)` on the inputs `1` and `2`, with the width-3 instance:
`R_F = 8` and `R_P = 57`, so 195 round constants. The values are computed when this book is
built, and the build fails if any differs from the text shown.

```lean
open Hash.ZK Hash.ZK.Poseidon.Circom

/-- A field element in hexadecimal. -/
def pHex (x : ZMod bn254) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 x.val)
```

The first round constant, and the first entry of the matrix:

```lean (name := pConsts)
#eval do
  let (cs, _) := samples 3
  IO.println cs.length
  IO.println (pHex (cs.getD 0 0 : ℕ))
  IO.println (pHex ((params 3).M 0 0))
```

```leanOutput pConsts
195
0xee9a592ba9a9518d05986d656f40c2114c4993c11bb29938d21d47304cd8e6e
0x109b7f411ba0e4c9b2b70caf5c36a7b194be7c11ad24378bfedb68592ba8118b
```

These are the first entries of circomlib's tables `C` and `M` for `t = 3`. The hash:

```lean (name := pHash)
#eval IO.println (pHex (poseidon 2 ![1, 2]))
```

```leanOutput pHash
0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a
```

This is the value in circomlib's test suite.

# Assurance status
%%%
tag := "poseidon-assurance"
%%%

The evidence that the Lean specification is circomlib's Poseidon, as of 2026-10-12:

:::table +header
*
  * Evidence
  * Status
*
  * Reference transcription
  * `Hash.ZK.Poseidon.Reference`, `Hash.ZK.Grain` and `Hash.ZK.Poseidon.Circom`, each definition
    citing its section of the paper, the reference script or circomlib.
*
  * Constants
  * Defined as the output of the Grain generator, as circomlib's were; checked against
    circomlib's tables by computation (the known-answer and differential tests), not proved
    in the kernel, which cannot evaluate the generator at this size.
*
  * Fast = reference
  * Proved in every commutative ring (`Hash.ZK.Poseidon.Fast.permutation_eq`), for CompPoly's
    Montgomery field (`HashZK.Poseidon.Circom.poseidon_eq`) and for the raw limbs of the C
    export (`HashZK.Raw.Poseidon.poseidonNat_eq`). The axiom audit shows only `propext`,
    `Classical.choice` and `Quot.sound`. The 32-byte encoding of the C export is not proved.
*
  * Streaming
  * Not applicable: circomlib's Poseidon hashes a fixed number of field elements.
*
  * Known-answer tests
  * 36 vectors for all sixteen widths, from go-iden3-crypto, light-poseidon and the reference
    implementation, pass through the specification over `ZMod p` and through CompPoly's field
    (`lake exe hash-kat`).
*
  * Differential testing
  * Every width, edge values (`0`, `p − 1`, `p`, $`2^{256} − 1`) and random inputs agree with
    `poseidon-rs` (all widths) and `light-poseidon` (up to 12 inputs).
*
  * Fuzzing
  * One `cargo-fuzz` target against both oracles; no divergence has been found. The roadmap's
    budget of $`10^9` executions has not yet been reached.
*
  * Known deviations
  * The reference script checks each matrix for infinitely long subspace trails and samples
    again on failure; the specification does not repeat the check. The first sample passes for
    every circomlib width, which the agreement with circomlib's matrices confirms. The C export
    reduces inputs modulo `p`, as the Rust oracles do; circomlib's circuits take field elements.
:::

# Security notes
%%%
tag := "poseidon-security"
%%%

This section points to the literature; it makes no claims of its own.

- *Round numbers.* The paper chooses `R_F` and `R_P` from statistical (differential, linear)
  and algebraic (interpolation, Gröbner basis) attacks, adds a security margin of two full rounds
  and 7.5% of the partial rounds, and circomlib rounds `R_P` up further (§5, §4.1).
- *Matrix.* Some Cauchy matrices let invariant subspaces pass through all partial rounds; the
  reference script tests for these "infinitely long subspace trails" and rejects such matrices
  (§2.3).
- *Cryptanalysis.* Bariant, Bouvier, Leurent and Perrin solve round-reduced CICO problems for
  Poseidon with algebraic attacks, in response to the Ethereum Foundation's bounties
  {citep bariant2022}[]. Their attacks do not reach the full round numbers.
- *Use as a hash.* circomlib's construction is a fixed-length compression of up to 16 elements.
  It is not a sponge, and it is collision resistant only for inputs of one fixed length.

# References
%%%
tag := "poseidon-references"
%%%

- L. Grassi, D. Khovratovich, C. Rechberger, A. Roy and M. Schofnegger, *Poseidon: A New Hash
  Function for Zero-Knowledge Proof Systems*, USENIX Security 2021; full version
  [ePrint 2019/458](https://eprint.iacr.org/2019/458).
- The Poseidon reference implementation, `generate_parameters_grain.sage`,
  [extgit.iaik.tugraz.at/krypto/hadeshash](https://extgit.iaik.tugraz.at/krypto/hadeshash).
- iden3, `circuits/poseidon.circom` and `circomlibjs`,
  [github.com/iden3/circomlib](https://github.com/iden3/circomlib).
- The known-answer vectors, `HashKAT/vectors/poseidon/circomlib-bn254.json`, with their
  provenance in `HashKAT/vectors/README.md`.

The papers cited in this chapter are listed in the book's bibliography.
