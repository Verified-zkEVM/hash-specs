/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import VersoManual
import Hash.Keccak.API
import Hash.Keccak.Constants
import Hash.Keccak.SHA3
import HashDocs.Bibliography

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open HashDocs.Bib

set_option pp.rawOnError true

#doc (Manual) "SHA-3 and Keccak" =>
%%%
tag := "sha3"
%%%

SHA-3 is the family of functions of FIPS 202, *SHA-3 Standard: Permutation-Based Hash and
Extendable-Output Functions*
([doi:10.6028/NIST.FIPS.202](https://doi.org/10.6028/NIST.FIPS.202)). This chapter explains the
standard alongside its Lean specification, `Hash.Keccak`. Section numbers in parentheses refer to
FIPS 202.

# Overview and history
%%%
tag := "sha3-overview"
%%%

Keccak was designed by Guido Bertoni, Joan Daemen, Michaël Peeters and Gilles Van Assche, and won
NIST's SHA-3 competition in 2012. FIPS 202 (2015) standardises four hash functions and two
*extendable-output functions* (XOFs), whose output can be as long as needed. All six are sponge
functions {citep bertoni2008}[] built on the permutation Keccak-f\[1600\]; they differ in the
capacity $`c` and in a few domain-separation bits appended to the message.

:::table +header
*
  * Function
  * Capacity $`c`
  * Rate (bytes)
  * Suffix
  * Output
  * Lean
*
  * SHA3-224
  * 448
  * 144
  * `01`
  * 224 bits
  * `Hash.sha3x224`
*
  * SHA3-256
  * 512
  * 136
  * `01`
  * 256 bits
  * `Hash.sha3x256`
*
  * SHA3-384
  * 768
  * 104
  * `01`
  * 384 bits
  * `Hash.sha3x384`
*
  * SHA3-512
  * 1024
  * 72
  * `01`
  * 512 bits
  * `Hash.sha3x512`
*
  * SHAKE128
  * 256
  * 168
  * `1111`
  * any
  * `Hash.shake128`
*
  * SHAKE256
  * 512
  * 136
  * `1111`
  * any
  * `Hash.shake256`
*
  * Keccak-256
  * 512
  * 136
  * none
  * 256 bits
  * `Hash.keccak256`
:::

Ethereum adopted Keccak before FIPS 202 added the domain-separation suffix, so Ethereum's
"SHA3" is the original Keccak-256, without the suffix. It is used for addresses, transaction and
block hashes, storage layout and the `KECCAK256` opcode, and its output differs from SHA3-256.

As in every chapter, the Lean specification has two layers. The *reference* specification
(`Hash.Keccak.KeccakP`, `Hash.Construction.Sponge`, `Hash.Keccak.SHA3`) transcribes the standard on
bit strings, for every width of the Keccak-p permutations. The *fast* specification
(`Hash.Keccak.Fast`) works on bytes and 64-bit lanes, and the functions `Hash.sha3x256` and so on
are defined by it. The two are proved equal for every function in the table (see
{ref "sha3-assurance"}[Assurance status]).

# Notation and data model
%%%
tag := "sha3-data-model"
%%%

FIPS 202 is specified on bit strings, and fixes a *least significant bit first* convention for
bytes (Appendix B.1): the byte `0x61` is the bit string `10000110`. Keccak-f\[1600\] works on 25
lanes of 64 bits, and with this convention eight consecutive message bytes form a lane in
little-endian order. This is the opposite of SHA-2, whose bytes are read most significant bit
first and whose words are big-endian.

![Bytes, bits and lanes in SHA-3](../static/keccak-data-model.svg)

In Lean, `Hash.bytesToBitsLSB` maps bytes to bits, and the fast specification loads lanes with
`Hash.ByteArray.getUInt64LE`.

# State and primitives
%%%
tag := "sha3-state"
%%%

The state of Keccak-p\[b, n\_r\] is a three-dimensional array of $`b = 25w` bits, $`A[x, y, z]` with
$`0 ≤ x, y < 5` and $`0 ≤ z < w`, where $`w = 2^ℓ` and $`ℓ ∈ \{0, …, 6\}` (§3.1). FIPS 202 names
its one- and two-dimensional parts:

![The Keccak state array](../static/keccak-state.svg)

The reference represents the state exactly so, as a function of the three coordinates:

{docstring Hash.Keccak.State}

The state is converted to and from a string of $`b` bits by $`S[w(5y + x) + z] = A[x, y, z]`
(§3.1.2, §3.1.3):

{docstring Hash.Keccak.State.ofString}

{docstring Hash.Keccak.State.toString}

# The round function
%%%
tag := "sha3-round"
%%%

One round applies five *step mappings*, $`\mathrm{Rnd}(A, i_r) = ι(χ(π(ρ(θ(A)))), i_r)` (§3.3).

## θ

θ XORs each bit with the parities of two nearby columns: column $`x − 1` of the same slice, and
column $`x + 1` of the previous slice (§3.2.1). It diffuses every bit to 11 others.

![The step mapping θ](../static/keccak-theta.svg)

{docstring Hash.Keccak.θ}

## ρ and π

ρ rotates each lane along $`z` by a fixed offset, and π permutes the lanes (§3.2.2, §3.2.3):

![The step mappings ρ and π](../static/keccak-rho-pi.svg)

{docstring Hash.Keccak.ρ}

{docstring Hash.Keccak.π}

## χ

χ is the only nonlinear step. Each row of five bits is transformed independently (§3.2.4):

![The step mapping χ on one row](../static/keccak-chi.svg)

{docstring Hash.Keccak.χ}

## ι

ι XORs a round constant into lane $`(0, 0)`, breaking the symmetry between rounds (§3.2.5). Its
bits come from a linear feedback shift register:

{docstring Hash.Keccak.rc}

{docstring Hash.Keccak.ι}

## The permutation

Keccak-p\[b, n\_r\] applies the last $`n_r` of the $`12 + 2ℓ` rounds, and Keccak-f\[b\] applies all of
them (§3.3, §3.4):

{docstring Hash.Keccak.keccakP}

# Mode of operation
%%%
tag := "sha3-mode"
%%%

The sponge construction SPONGE\[f, pad, r\] turns the permutation into a function with output of
any length (§4). The state is split into the *rate* $`r` and the *capacity* $`c = b − r`. The
padded message is absorbed $`r` bits at a time, with $`f` applied after each block, and the
output is squeezed out $`r` bits at a time, with $`f` applied between blocks:

![The sponge construction](../static/keccak-sponge.svg)

{docstring Hash.Sponge.sponge}

The padding rule is pad10\*1 (§5.1), and KECCAK\[c\] is the sponge on Keccak-f\[1600\] with rate
$`1600 − c` (§5.2):

{docstring Hash.Sponge.pad101}

{docstring Hash.Keccak.Reference.keccak}

The six functions of FIPS 202 append their suffix to the message and call KECCAK\[c\] (§6.1,
§6.2); for example

{docstring Hash.Keccak.Reference.sha3x256}

{docstring Hash.Keccak.Reference.shake128}

An XOF's shorter outputs are prefixes of its longer ones: `Hash.Keccak.Reference.shake128_prefix`
proves this for the reference, and `Hash.Keccak.shake128_prefix` for the byte-level function.
The library also has a streaming interface, `Hash.Keccak.Fast.State`, with initial states such as
`Hash.sha3x256Init`.

# Parameters and constants
%%%
tag := "sha3-constants"
%%%

Keccak has two sets of constants, both derived rather than chosen. The ρ offsets are the
triangular numbers $`(t + 1)(t + 2)/2`, assigned to the lanes in the order of a walk
$`(x, y) ← (y, (2x + 3y) \bmod 5)` (§3.2.2). The round constants are outputs of the LFSR of
Algorithm 5. The library writes both as tables, as they are usually printed, and proves them
equal to their derivations by kernel computation:

```lean
open Hash Hash.Keccak in
example :
    roundConstants = (List.range 24).map fun ir =>
      ((List.range 64).map fun z =>
        if RC 6 (ir : Nat) z then 2 ^ z else 0).sum :=
  roundConstants_eq
```

The ρ table is `Hash.Keccak.rhoOffsets`, proved equal to the offsets of Algorithm 2 by
`Hash.Keccak.rhoOffsets_eq`.

# Worked example
%%%
tag := "sha3-example"
%%%

We trace SHA3-256 on the message `abc`, one block of NIST's
[example values](https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines/example-values).
The values are computed by the fast specification when this book is built, and the build fails
if any differs from the text shown.

```lean
open Hash Hash.Keccak.Fast

/-- A lane as sixteen hexadecimal digits. -/
def hex16 (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  String.ofList (List.replicate (16 - s.length) '0')
    ++ s

/-- Print lanes separated by spaces. -/
def printLanes (ls : List UInt64) : IO Unit :=
  IO.println (" ".intercalate (ls.map hex16))

def abcBytes : ByteArray := ⟨#[0x61, 0x62, 0x63]⟩
```

Padding to the 136-byte rate appends the byte `0x06` (the suffix `01` and the first bit of
pad10\*1), zeros, and `0x80` (the last bit of pad10\*1):

```lean (name := padded3)
def block : ByteArray := pad 136 0x06 abcBytes

#eval IO.println block.toHex
```

```leanOutput padded3
61626306000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080
```

XORed into the all-zero state, the block fills the first 17 lanes. Lane 0 holds the message
bytes in little-endian order, and lane 16 the final padding bit:

```lean (name := absorbed)
def a₀ : Array UInt64 := tabulate 25 fun i =>
  if i < 17 then ByteArray.getUInt64LE block (8 * i)
  else 0

#eval printLanes [lane a₀ 0, lane a₀ 1, lane a₀ 16]
```

```leanOutput absorbed
0000000006636261 0000000000000000 8000000000000000
```

The first round's θ step spreads lane 16's bit, which lies in column 1, into every lane of
columns 0 and 2. Lanes 0 to 4 after θ, and after the whole first round:

```lean (name := round0)
#eval do
  printLanes ((theta a₀).toList.take 5)
  printLanes ((round a₀ 0).toList.take 5)
```

```leanOutput round0
0000000006636260 0000000006636261 8000000000000000 0000000000000000 000000000cc6c4c2
0000040006636261 3626100000000066 00000731b1308000 0000000006436260 36261331b1308006
```

After all 24 rounds, the first four lanes, read as little-endian bytes, are the digest:

```lean (name := digest3)
#eval do
  printLanes ((keccakF a₀).toList.take 4)
  IO.println (sha3x256 abcBytes).toHex
```

```leanOutput digest3
b225e24fa75d983a bd90d36b2d175c04 5b529d3e6e085f85 3215431145e2bf46
3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532
```

# Assurance status
%%%
tag := "sha3-assurance"
%%%

The evidence that the Lean specification is the SHA-3 of FIPS 202, as of 2026-10-12:

:::table +header
*
  * Evidence
  * Status
*
  * Reference transcription
  * `Hash.Keccak.KeccakP`, `Hash.Construction.Sponge` and `Hash.Keccak.SHA3`, for every width
    $`b ∈ \{25, …, 1600\}` and number of rounds, each definition citing its section of FIPS 202.
    `Hash.Keccak.keccakP_eq_algorithm7` shows that the evaluated form is Algorithm 7 as written.
*
  * Constants
  * The ρ offsets and the round constants are proved equal to Algorithms 2 and 5–6.
*
  * Fast = reference
  * Proved for all seven functions: `Hash.Keccak.sha3x224_eq` to `Hash.Keccak.keccak256_eq`,
    from `Hash.Keccak.Equiv.keccakP_toString` (lanes against state arrays) and
    `Hash.Keccak.Equiv.sponge_eq` (bytes against bits). The axiom audit shows only `propext`,
    `Classical.choice` and `Quot.sound`.
*
  * Further properties
  * Keccak-p\[b, n\_r\] is a bijection for every $`b` (`Hash.Keccak.keccakPState_bijective`,
    `Hash.Keccak.keccakP_injective`, `Hash.Keccak.keccakP_surjective`). SHAKE128 and SHAKE256
    are prefix-consistent, on bits and on bytes.
*
  * Known-answer tests
  * All 4642 NIST CAVP SHA3VS vectors (short and long messages, variable output and Monte
    Carlo) pass, and the 4042 message vectors pass again through the streaming interface in five
    splitting patterns (`lake exe hash-kat`). Keccak-256 has no NIST vectors; it is covered by
    differential testing and a kernel-checked example.
*
  * Differential testing
  * Every message length up to 505 bytes, XOF output lengths around the rate boundaries, a 1 MiB
    message, random messages and random streaming splits agree with RustCrypto `sha3`,
    `tiny-keccak`, AWS-LC (SHA3-256/384/512) and `alloy-primitives` (Keccak-256).
*
  * Fuzzing
  * Two `cargo-fuzz` targets (one-shot and streaming), run nightly in CI; no divergence has been
    found. The roadmap's budget of $`10^9` executions per oracle has not yet been reached.
*
  * Other formal specifications
  * EasyCrypt and Jasmin (Almeida et al. {citep almeida2019}[]), F\* (HACL\*), Cryptol, ACL2,
    and several Lean specifications of Keccak-256 and SHA-3 (informational; see
    `LIT-REVIEW.md`).
*
  * Known deviations
  * The fast specification takes byte strings, so messages whose length is not a multiple of 8
    bits are covered only by the reference specification.
:::

# Security notes
%%%
tag := "sha3-security"
%%%

This section points to the literature; it makes no claims of its own.

- *Generic security.* The sponge construction with a random permutation is indifferentiable
  from a random oracle up to about $`2^{c/2}` queries {citep bertoni2008}[]. Almeida et al. give a
  machine-checked proof of this indifferentiability result in EasyCrypt {citep almeida2019}[].
- *Security strengths.* FIPS 202 (Appendix A.1) lists the collision, preimage and second
  preimage strengths of each function; for SHAKE these depend on the output length as well as
  the capacity.
- *No length extension.* Only the rate part of the state is output, so the capacity is never
  revealed, and the length-extension property of Merkle–Damgård hashes such as SHA-256 does not
  apply.
- *Cryptanalysis of reduced-round variants.* Practical collision attacks exist on SHA-3 instances
  reduced to a few of the 24 rounds; for example, Guo et al. extend earlier connector-based
  attacks to collisions on up to 6 rounds of some Keccak instances
  ([doi:10.1007/s00145-019-09313-3](https://doi.org/10.1007/s00145-019-09313-3)). None of these
  reaches the full 24 rounds.

# References
%%%
tag := "sha3-references"
%%%

- NIST, *SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions*, FIPS PUB 202,
  2015. [doi:10.6028/NIST.FIPS.202](https://doi.org/10.6028/NIST.FIPS.202)
- G. Bertoni, J. Daemen, M. Peeters and G. Van Assche, *The Keccak Reference*, version 3.0,
  2011. [keccak.team](https://keccak.team/files/Keccak-reference-3.0.pdf)
- NIST, Cryptographic Algorithm Validation Program, *SHA-3 Validation System test vectors*.
  Vendored in `HashKAT/vectors/nist-cavp-sha3/`.

The papers cited in this chapter are listed in the book's bibliography.
