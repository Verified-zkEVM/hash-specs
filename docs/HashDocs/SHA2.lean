/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import VersoManual
import Hash.Construction.MerkleDamgard
import Hash.SHA2.API
import Hash.SHA2.Constants
import HashDocs.Bibliography

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open HashDocs.Bib

set_option pp.rawOnError true

#doc (Manual) "SHA-2" =>
%%%
tag := "sha2"
%%%

SHA-2 is the family of hash functions of the *Secure Hash Standard*, FIPS 180-4
([doi:10.6028/NIST.FIPS.180-4](https://doi.org/10.6028/NIST.FIPS.180-4)). This chapter explains
the standard alongside its Lean specification, `Hash.SHA2`. Section numbers in parentheses, such
as (§6.2.2), refer to FIPS 180-4.

# Overview and history
%%%
tag := "sha2-overview"
%%%

SHA-2 was designed by the U.S. National Security Agency and published by NIST in FIPS 180-2
(2002), alongside SHA-1. SHA-224 was added in 2004, and SHA-512/224 and SHA-512/256
in FIPS 180-4 (2012; the current revision is from 2015). The six members share one design: a
Merkle–Damgård iteration {citep merkle1989 damgard1989}[] of a compression function built from
32-bit or 64-bit word operations.

:::table +header
*
  * Member
  * Word size
  * Rounds
  * Block
  * Digest
  * Lean
*
  * SHA-224
  * 32
  * 64
  * 512
  * 224
  * `Hash.sha224`
*
  * SHA-256
  * 32
  * 64
  * 512
  * 256
  * `Hash.sha256`
*
  * SHA-384
  * 64
  * 80
  * 1024
  * 384
  * `Hash.sha384`
*
  * SHA-512
  * 64
  * 80
  * 1024
  * 512
  * `Hash.sha512`
*
  * SHA-512/224
  * 64
  * 80
  * 1024
  * 224
  * `Hash.sha512t224`
*
  * SHA-512/256
  * 64
  * 80
  * 1024
  * 256
  * `Hash.sha512t256`
:::

SHA-256 is used throughout Bitcoin, in TLS and code signing, and in Ethereum as the `SHA256`
precompile at address `0x02`; zkVMs commonly provide it as an accelerated circuit.

The Lean specification has two layers, as in every chapter of this book:

- The *reference* specification, `Hash.SHA2.Reference`, transcribes the standard: messages are
  bit strings (`List Bool`) and words are bit vectors (`BitVec w`). It is written once for the
  whole family, parameterised by `Hash.SHA2.Params`.
- The *fast* specification, `Hash.SHA2.Fast`, computes the same function on byte arrays and
  `UInt32` or `UInt64` words. The functions `Hash.sha256` and so on are defined by it.

The theorem `Hash.SHA2.Equiv.hashWith_eq` proves that the two agree on every byte string (see
{ref "sha2-assurance"}[Assurance status]).

# Notation and data model
%%%
tag := "sha2-data-model"
%%%

FIPS 180-4 works with bit strings and $`w`-bit words, where $`w = 32` or $`w = 64` (§2.1). Two
conventions fix how bytes, bits and words correspond (§3.1), and they are the most common source
of errors in implementations:

- A byte is read *most significant bit first*: the byte `0x61` is the bit string `01100001`.
- A word is formed from consecutive bytes in *big-endian* order: the first byte is the most
  significant.

![Bytes, bits and words in SHA-2](../static/sha2-data-model.svg)

In Lean, `Hash.bytesToBitsMSB` maps a list of bytes to its bit string, and the fast
specification loads words with `Hash.ByteArray.getUInt32BE` and `Hash.ByteArray.getUInt64BE`.
The equivalence proof shows that these agree with the reference's parsing of bit strings into
words:

{docstring Hash.SHA2.Reference.parse}

All arithmetic on words is modulo $`2^w`, and the bitwise operations are those of `BitVec w`.

# State and primitives
%%%
tag := "sha2-primitives"
%%%

The state between blocks is the *hash value* $`H^{(i)}`, eight words. Within a block, the
compression function works on eight *working variables* $`a, b, …, h`:

{docstring Hash.SHA2.Reference.Vars}

It uses six functions on words (§4.1.2, §4.1.3). $`\mathrm{Ch}(x, y, z)` chooses, bit by bit,
$`y` where $`x` is 1 and $`z` where $`x` is 0; $`\mathrm{Maj}(x, y, z)` is the bitwise majority:

{docstring Hash.SHA2.Reference.Ch}

{docstring Hash.SHA2.Reference.Maj}

The functions $`\Sigma_0, \Sigma_1` (used in the round) and $`\sigma_0, \sigma_1` (used in the
message schedule) XOR together rotations and shifts of their argument. The reference states their
shape once, with the amounts as parameters:

{docstring Hash.SHA2.Reference.bigSigma}

{docstring Hash.SHA2.Reference.smallSigma}

:::table +header
*
  * Function
  * 32-bit words
  * 64-bit words
*
  * $`\Sigma_0`
  * ROTR 2, 13, 22
  * ROTR 28, 34, 39
*
  * $`\Sigma_1`
  * ROTR 6, 11, 25
  * ROTR 14, 18, 41
*
  * $`\sigma_0`
  * ROTR 7, 18; SHR 3
  * ROTR 1, 8; SHR 7
*
  * $`\sigma_1`
  * ROTR 17, 19; SHR 10
  * ROTR 19, 61; SHR 6
:::

# The compression function
%%%
tag := "sha2-compression"
%%%

The compression function processes one block of sixteen words $`M_0, …, M_{15}` (§6.2.2,
§6.4.2). It has three steps: expand the block into a message schedule, run the rounds, and add
the result into the hash value.

## The message schedule

The schedule has one word $`W_t` per round. The first sixteen are the block itself; each later
word mixes four earlier ones:

![The SHA-2 message schedule](../static/sha2-schedule.svg)

{docstring Hash.SHA2.Reference.schedule}

## The round function

Each round updates the working variables using the round constant $`K_t` and the schedule word
$`W_t`. Two temporaries are computed, $`T_1 = h + \Sigma_1(e) + \mathrm{Ch}(e, f, g) + K_t + W_t`
and $`T_2 = \Sigma_0(a) + \mathrm{Maj}(a, b, c)`; then every variable shifts down one place,
except that $`e` gains $`T_1` and the new $`a` is $`T_1 + T_2`:

![One round of the SHA-2 compression function](../static/sha2-round.svg)

{docstring Hash.SHA2.Reference.round}

## Adding into the hash value

After the last round, each working variable is added to the corresponding word of the hash
value. This feed-forward makes the compression function one-way even though each round is
invertible:

{docstring Hash.SHA2.Reference.compress}

# Mode of operation
%%%
tag := "sha2-mode"
%%%

## Padding

The message is first padded to a whole number of blocks (§5.1). For SHA-224 and SHA-256, a
message of $`\ell` bits is followed by a single 1 bit, then the least number $`k` of zero bits
that leaves 64 bits before a block boundary, then $`\ell` as a 64-bit big-endian number. The
64-bit members use 1024-bit blocks and a 128-bit length field.

![SHA-256 padding](../static/sha2-padding.svg)

{docstring Hash.SHA2.Reference.pad}

## The Merkle–Damgård iteration

The padded message is parsed into blocks $`M^{(1)}, …, M^{(N)}` (§5.2). Starting from the
initial hash value $`H^{(0)}`, each block is compressed into the hash value in turn, and the
digest is the leftmost bits of $`H^{(N)}` (§6.2.2, §6.3, §6.4.2, §6.5–6.7):

![The Merkle–Damgård iteration](../static/sha2-md.svg)

{docstring Hash.SHA2.Reference.hash}

The iteration itself is `Hash.MerkleDamgard.iterate`, shared with any other Merkle–Damgård hash.
Because iteration can resume from any intermediate hash value
(`Hash.MerkleDamgard.iterate_append`), a message can be hashed incrementally; the library's
streaming interface is `Hash.SHA2.Fast.State`, with initial states such as `Hash.sha256Init`.

# Parameters and constants
%%%
tag := "sha2-constants"
%%%

The members differ only in their parameters:

{docstring Hash.SHA2.Params}

The constants are "nothing up my sleeve" numbers (§4.2.2, §4.2.3, §5.3). The round constants of
SHA-224/256 are the first 32 bits of the fractional parts of the cube roots of the first 64
primes; those of the 64-bit members are the first 64 bits for the first 80 primes. The initial
hash values of SHA-256 and SHA-512 come from the square roots of the first 8 primes, and those
of SHA-224 and SHA-384 from the 9th to 16th primes.

The library writes each table out as printed in the standard, so that it can be compared by eye,
and proves it equal to its derivation by kernel computation. For example, the theorem
`Hash.SHA2.K256_eq` states

```lean
open Hash Hash.SHA2 in
example :
    K256 = (first80Primes.take 64).map
      (fracRootBits 3 32) :=
  K256_eq
```

where `Hash.fracRootBits k w p` is the first $`w` bits of the fractional part of $`p^{1/k}`,
computed with integer roots.

The initial values of SHA-512/224 and SHA-512/256 are generated by the *SHA-512/t IV generation
function* (§5.3.6): SHA-512, with its initial value XORed with `a5a5a5a5a5a5a5a5`, applied to
the ASCII string `SHA-512/t`. This too is a theorem:

```lean
open Hash Hash.SHA2 in
example :
    initialHash512t256 = sha512tIV
      ("SHA-512/256".toList.map fun c =>
        c.toNat.toUInt8) :=
  initialHash512t256_eq
```

# Worked example
%%%
tag := "sha2-example"
%%%

We trace SHA-256 on the three-byte message `abc`, the first example of NIST's
[example values](https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines/example-values).
Every value below is computed by the fast specification when this book is built, and the build
fails if any output differs from the text shown.

```lean
open Hash Hash.SHA2
open Hash.SHA2.Reference (Vars)

/-- A word as eight hexadecimal digits. -/
def hex8 (x : UInt32) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  String.ofList (List.replicate (8 - s.length) '0')
    ++ s

/-- Print words separated by spaces. -/
def printWords (ws : List UInt32) : IO Unit :=
  IO.println (" ".intercalate (ws.map hex8))

def abc : ByteArray := ⟨#[0x61, 0x62, 0x63]⟩
```

Padding gives a single 512-bit block: the message, the byte `0x80` (the 1 bit and seven zero
bits), zeros, and the length 24 = `0x18`:

```lean (name := padded)
#eval IO.println (Fast.pad sha256 abc).toHex
```

```leanOutput padded
61626380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018
```

The block's sixteen words are the first sixteen schedule words; the next ones are mixed from
them:

```lean (name := sched)
def W : Array UInt32 :=
  Fast.schedule sha256 (Fast.pad sha256 abc) 0

#eval do
  printWords (W.toList.take 16)
  printWords ((W.toList.drop 16).take 4)
```

```leanOutput sched
61626380 00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000018
61626380 000f0000 7da86405 600003c6
```

The working variables start as $`H^{(0)}`. After rounds $`t = 0`, $`t = 1` and $`t = 63` they
are as follows (in the order $`a, …, h`), matching NIST's published intermediate values:

```lean (name := rounds)
def K : Array UInt32 :=
  (sha256.K.map UInt32.ofNat).toArray

def v₀ : Vars UInt32 :=
  let H := sha256.H0.map UInt32.ofNat
  ⟨H[0]!, H[1]!, H[2]!, H[3]!,
    H[4]!, H[5]!, H[6]!, H[7]!⟩

def after (t : Nat) : Vars UInt32 :=
  (List.range (t + 1)).foldl
    (Fast.round sha256 K W) v₀

def printVars (v : Vars UInt32) : IO Unit :=
  printWords [v.a, v.b, v.c, v.d, v.e, v.f, v.g, v.h]

#eval do
  printVars (after 0)
  printVars (after 1)
  printVars (after 63)
```

```leanOutput rounds
5d6aebcd 6a09e667 bb67ae85 3c6ef372 fa2a4622 510e527f 9b05688c 1f83d9ab
5a6ad9ad 5d6aebcd 6a09e667 bb67ae85 78ce7989 fa2a4622 510e527f 9b05688c
506e3058 d39a2165 04d24d6c b85e2ce9 5ef50f24 fb121210 948d25b6 961f4894
```

Adding these into $`H^{(0)}` gives the digest:

```lean (name := digest)
#eval IO.println (sha256 abc).toHex
```

```leanOutput digest
ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
```

The same digest is also checked by the kernel, so it holds as a theorem rather than only as a
computation:

```lean
example :
    (sha256 abc).toHex =
      "ba7816bf8f01cfea414140de5dae2223" ++
      "b00361a396177a9cb410ff61f20015ad" := by
  decide +kernel
```

# Assurance status
%%%
tag := "sha2-assurance"
%%%

The evidence that the Lean specification is the SHA-2 of FIPS 180-4, as of 2026-10-12:

:::table +header
*
  * Evidence
  * Status
*
  * Reference transcription
  * `Hash.SHA2.Reference`, every definition citing its section of FIPS 180-4.
*
  * Constants
  * All tables proved equal to their derivations, including the SHA-512/t IV generation
    (`Hash.SHA2.K256_eq`, `Hash.SHA2.initialHash512t224_eq` and others).
*
  * Fast = reference
  * Proved for all six members: `Hash.SHA2.sha224_eq` to `Hash.SHA2.sha512t256_eq`, from the
    generic `Hash.SHA2.Equiv.hashWith_eq`. Streaming equals one-shot for every way of splitting
    the message (`Hash.SHA2.Fast.State.finalize_updates`, and `Hash.sha256Init_eq` and so on
    for the byte-level API). The axiom audit (`HashTests/Axioms.lean`) shows only
    `propext`, `Classical.choice` and `Quot.sound`.
*
  * Known-answer tests
  * All 1886 NIST CAVP SHAVS vectors (short messages, long messages and Monte Carlo) for all six
    members pass, and the 1286 message vectors pass again through the streaming interface in five
    splitting patterns (`lake exe hash-kat`). Eleven examples are also checked by the kernel.
*
  * Differential testing
  * Every message length up to 385 bytes, a 1 MiB message, random messages and random streaming
    splits agree with RustCrypto `sha2` and AWS-LC.
*
  * Fuzzing
  * Two `cargo-fuzz` targets (one-shot and streaming) against RustCrypto `sha2` and AWS-LC, run
    nightly in CI; no divergence has been found. The roadmap's budget of $`10^9` executions per
    oracle has not yet been reached.
*
  * Other formal specifications
  * Coq (Appel {citep appel2015}[]), F\* (HACL\*), Isabelle (AFP `Crypto_Standards`), Cryptol,
    ACL2, and the Lean specifications of the SymCrypt/Aeneas and OpenVM projects
    (informational; see `LIT-REVIEW.md`).
*
  * Known deviations
  * The fast specification takes byte strings, so messages whose length is not a multiple of 8
    bits are covered only by the reference specification.
:::

# Security notes
%%%
tag := "sha2-security"
%%%

This section points to the literature; it makes no claims of its own.

- *Security strengths.* NIST SP 800-107 Revision 1
  ([doi:10.6028/NIST.SP.800-107r1](https://doi.org/10.6028/NIST.SP.800-107r1)) gives the
  collision resistance of a SHA-2 member with an $`L`-bit digest as $`L/2` bits, and its
  preimage resistance as $`L` bits.
- *Length extension.* SHA-256 and SHA-512 output their whole final hash value, so, as for any
  plain Merkle–Damgård hash, $`H(M \| \mathrm{pad} \| X)` can be computed from $`H(M)` and the
  length of $`M` without knowing $`M`. Coron et al. show that Merkle–Damgård is not
  indifferentiable from a random oracle, and that truncating the output, as SHA-224, SHA-384 and
  SHA-512/t do, is one remedy {citep coron2005}[]. Use HMAC (FIPS 198-1) rather than
  $`H(\mathit{key} \| M)` as a MAC.
- *Cryptanalysis of step-reduced variants.* Published attacks include a collision for 31 of the
  64 steps of SHA-256 and a semi-free-start collision for 38 steps {citep mendel2013}[], a
  practical semi-free-start collision for 39 steps of SHA-256 and collisions for 31 steps of
  SHA-512 {citep li2024}[], and biclique preimage attacks on step-reduced SHA-2
  {citep khovratovich2012}[]. None of these reaches the full number of steps.
- *Implementations.* Appel verified OpenSSL's SHA-256 against a Coq transcription of FIPS 180-4
  {citep appel2015}[]; the fast specification here is a specification, not a constant-time
  production implementation.

# References
%%%
tag := "sha2-references"
%%%

- NIST, *Secure Hash Standard (SHS)*, FIPS PUB 180-4, 2015.
  [doi:10.6028/NIST.FIPS.180-4](https://doi.org/10.6028/NIST.FIPS.180-4)
- NIST, *Recommendation for Applications Using Approved Hash Algorithms*, SP 800-107 Rev. 1,
  2012. [doi:10.6028/NIST.SP.800-107r1](https://doi.org/10.6028/NIST.SP.800-107r1)
- NIST, *The Keyed-Hash Message Authentication Code (HMAC)*, FIPS PUB 198-1, 2008.
  [doi:10.6028/NIST.FIPS.198-1](https://doi.org/10.6028/NIST.FIPS.198-1)
- NIST, Cryptographic Algorithm Validation Program, *Secure Hash Algorithm Validation System
  test vectors*. Vendored in `HashKAT/vectors/nist-cavp-shs/`.

The papers cited in this chapter are listed in the book's bibliography.
