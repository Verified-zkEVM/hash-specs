/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import VersoManual
import Hash.BLAKE2.API
import Hash.BLAKE2.Constants
import HashDocs.Bibliography

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open HashDocs.Bib

set_option pp.rawOnError true

#doc (Manual) "BLAKE2" =>
%%%
tag := "blake2"
%%%

BLAKE2 is the hash family of RFC 7693, *The BLAKE2 Cryptographic Hash and Message Authentication
Code (MAC)* ([doi:10.17487/RFC7693](https://doi.org/10.17487/RFC7693)), extended with the
parameter block of the BLAKE2 specification {citep aumasson2013}[]. This chapter explains the
standard alongside its Lean specification, `Hash.BLAKE2`. Section numbers in parentheses refer
to RFC 7693.

# Overview and history
%%%
tag := "blake2-overview"
%%%

BLAKE was a finalist of NIST's SHA-3 competition. In 2012 Jean-Philippe Aumasson, Samuel Neves,
Zooko Wilcox-O'Hearn and Christian Winnerlein published BLAKE2, a faster revision with fewer
rounds, simpler padding, and a built-in keyed mode and parameter block {citep aumasson2013}[].
RFC 7693 (2015) specifies the two main variants. BLAKE2 is used by the Argon2 password hash,
by WireGuard (BLAKE2s), and by Zcash (personalised BLAKE2b). Ethereum's Istanbul upgrade added
a precompile for the BLAKE2b compression function $`F` (EIP-152), with a caller-chosen number
of rounds, for interoperability with Zcash.

:::table +header
*
  * Function
  * Word
  * Rounds
  * Block
  * Output
  * Key
  * Lean
*
  * BLAKE2b
  * 64 bits
  * 12
  * 128 bytes
  * 1–64 bytes
  * 0–64 bytes
  * `Hash.blake2bWith`, `Hash.blake2b`
*
  * BLAKE2s
  * 32 bits
  * 10
  * 64 bytes
  * 1–32 bytes
  * 0–32 bytes
  * `Hash.blake2sWith`, `Hash.blake2s`
*
  * BLAKE2b `F` (EIP-152)
  * 64 bits
  * any
  * 128 bytes
  * 64 bytes
  * none
  * `Hash.blake2bPrecompile`
:::

The *reference* specification (`Hash.BLAKE2.Reference`) transcribes RFC 7693 on bit vectors
and byte lists, for both word sizes and any number of rounds. The *fast* specification
(`Hash.BLAKE2.Fast`) works on byte arrays and machine words, generic over `UInt64` and
`UInt32`, and the functions of the table are defined by it. The two are proved equal (see
{ref "blake2-assurance"}[Assurance status]).

# Notation and data model
%%%
tag := "blake2-data-model"
%%%

BLAKE2 reads bytes as $`w`-bit words in little-endian order: the first byte of a word is its
least significant (§2.4). The digest is the final chain value written out in the same order.

![Bytes and words in BLAKE2](../static/blake2-data-model.svg)

{docstring Hash.BLAKE2.Reference.wordsLE}

{docstring Hash.BLAKE2.Reference.bytesLE}

The output length, the key length, a salt and a personalisation string enter the hash through
the *parameter block*, which is XORed into the initialization vector (§2.5, and §2.5 of the
BLAKE2 specification). RFC 7693 fixes the salt and personalisation to zero; the Lean
specification takes them as arguments.

![The BLAKE2b parameter block](../static/blake2-params.svg)

{docstring Hash.BLAKE2.Reference.paramBlock}

# State and primitives
%%%
tag := "blake2-state"
%%%

The parameters that distinguish BLAKE2b from BLAKE2s are collected in one structure, and the
specification is written once for both:

{docstring Hash.BLAKE2.Params}

The compression function works on a *work vector* of sixteen words, drawn as a 4×4 matrix. Its
top half is the chain value $`h`, its bottom half the initialization vector; the byte counter
$`t` is XORed into words 12 and 13, and word 14 is inverted for the last block (§3.2).

![The BLAKE2 work vector](../static/blake2-state.svg)

# The round function
%%%
tag := "blake2-round"
%%%

The mixing function $`G` updates four words of the work vector with two message words, using
additions modulo $`2^w`, exclusive or and rotations (§3.1):

![The mixing function G](../static/blake2-g.svg)

{docstring Hash.BLAKE2.Reference.G}

A round applies $`G` to the four columns of the work vector, then to the four diagonals, with
message words chosen by the permutation $`\sigma_{i \bmod 10}` (§3.2):

{docstring Hash.BLAKE2.SIGMA}

{docstring Hash.BLAKE2.Reference.round}

The compression function $`F` initialises the work vector, applies the rounds, and XORs the two
halves into the chain value. Its round count is an argument, as in EIP-152:

{docstring Hash.BLAKE2.Reference.F}

# Mode of operation
%%%
tag := "blake2-mode"
%%%

BLAKE2 iterates $`F` over the data blocks, a Merkle–Damgård-style chain with two
differences: the byte counter $`t` is an input to every compression, and the last block is
marked by the final flag $`f`, so no length padding is needed (§3.3). A key, if any, is padded to
a whole block and processed first, which makes keyed BLAKE2 a MAC without the nested
construction of HMAC.

![BLAKE2 hashing](../static/blake2-mode.svg)

{docstring Hash.BLAKE2.Reference.blocks}

{docstring Hash.BLAKE2.Reference.hash}

The library also has a streaming interface, `Hash.BLAKE2.Fast.State`, with initial states
`Hash.blake2bInit` and `Hash.blake2sInit`. Because the last block must be compressed with the
final flag, the state holds back the pending block until more input arrives or `finalize` is
called. Ethereum's precompile parses its 213-byte input and calls the fast $`F`:

{docstring Hash.blake2bPrecompile}

# Parameters and constants
%%%
tag := "blake2-constants"
%%%

The two instances are:

{docstring Hash.BLAKE2.blake2bParams}

{docstring Hash.BLAKE2.blake2sParams}

Their initialization vectors are the SHA-512 and SHA-256 initial hash values (§2.6), the first
64 or 32 bits of the fractional parts of the square roots of the first eight primes. The library
proves this by kernel computation:

```lean
open Hash in
example :
    BLAKE2.blake2bParams.IV =
      SHA2.initialHash512 :=
  BLAKE2.blake2b_IV
```

`Hash.BLAKE2.blake2s_IV` is the same for BLAKE2s. The ten message permutations come from BLAKE;
`Hash.BLAKE2.SIGMA_perm` checks that each is a permutation of the sixteen word indices. The
rotation constants $`(R_1, R_2, R_3, R_4)` were chosen for speed {citep aumasson2013}[].

# Worked example
%%%
tag := "blake2-example"
%%%

We trace BLAKE2b-512 on the message `abc`, the example of RFC 7693 Appendix A. The values are
computed by the fast specification when this book is built, and the build fails if any differs
from the text shown. Every value below agrees with the RFC.

```lean
open Hash Hash.BLAKE2 Hash.BLAKE2.Fast

/-- A word as sixteen hexadecimal digits. -/
def b2hex (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  String.ofList (List.replicate (16 - s.length) '0')
    ++ s

/-- Print words, four per line. -/
def b2print (ws : List UInt64) : IO Unit :=
  for i in [0:ws.length:4] do
    IO.println (" ".intercalate
      ((ws.drop i).take 4 |>.map b2hex))

def b2abc : ByteArray := ⟨#[0x61, 0x62, 0x63]⟩
```

The parameter block for a 64-byte digest without key starts with the bytes `40 00 01 01`, so
$`h_0` differs from the IV only in its first word:

```lean (name := b2h0)
def b2pb : ByteArray :=
  paramBlock blake2bParams 64 0 .empty .empty

def b2h0 : Array UInt64 :=
  ((List.range 8).map fun i =>
    Word.xor (Word.ofNat (blake2bParams.IV.getD i 0))
      (Word.loadLE b2pb (i * 8))).toArray

#eval do
  IO.println (b2pb.extract 0 4).toHex
  b2print b2h0.toList
```

```leanOutput b2h0
40000101
6a09e667f2bdc948 bb67ae8584caa73b 3c6ef372fe94f82b a54ff53a5f1d36f1
510e527fade682d1 9b05688c2b3e6c1f 1f83d9abfb41bd6b 5be0cd19137e2179
```

The message is one zero-padded block whose first word is `0x0000000000636261`. The work vector
starts as $`h_0` followed by the IV, with $`t = 3` XORed into word 12 and word 14 inverted:

```lean (name := b2v0)
def b2m : Array UInt64 :=
  block blake2bParams (pad blake2bParams .empty b2abc) 0

def b2v0 : Array UInt64 :=
  let v := b2h0 ++ (blake2bParams.IV.map Word.ofNat).toArray
  let v := v.set! 12 (Word.xor (get v 12) (Word.ofNat 3))
  v.set! 14 (Word.not (get v 14))

#eval b2print b2v0.toList
```

```leanOutput b2v0
6a09e667f2bdc948 bb67ae8584caa73b 3c6ef372fe94f82b a54ff53a5f1d36f1
510e527fade682d1 9b05688c2b3e6c1f 1f83d9abfb41bd6b 5be0cd19137e2179
6a09e667f3bcc908 bb67ae8584caa73b 3c6ef372fe94f82b a54ff53a5f1d36f1
510e527fade682d2 9b05688c2b3e6c1f e07c265404be4294 5be0cd19137e2179
```

After the first round:

```lean (name := b2v1)
#eval b2print (round blake2bParams b2m b2v0 0).toList
```

```leanOutput b2v1
86b7c1568029bb79 c12cbcc809ff59f3 c6a5214cc0eaca8e 0c87cd524c14cc5d
44ee6039bd86a9f7 a447c850aa694a7e de080f1bb1c0f84b 595cb8a9a1aca66c
bec3ae837eac4887 6267fc79df9d6ad1 fa87b01273fa6dbe 521a715c63e08d8a
e02d0975b8d37a83 1c7b754f08b7d193 8f885a76b6e578fe 2318a24e2140fc64
```

After all twelve rounds, the two halves are XORed into $`h_0`, and the result, written out in
little-endian order, is the digest:

```lean (name := b2digest)
#eval do
  b2print ((List.range 12).foldl
    (round blake2bParams b2m) b2v0).toList
  IO.println (blake2b b2abc).toHex
```

```leanOutput b2digest
12ef8a641ec4f6d6 bced5de977c9faf5 733ca476c5148639 97df596b0610f6fc
f42c16519ad5afa7 aa5ac1888e10467e 217d930aa51787f3 906a6ff19e573942
75ab709bd3dcbf24 ee7ce1f345947aa4 f8960d6c2faf5f5e e332538a36b6d246
885bef040ef6aa0b a4939a417bfb78a3 646cbb7af6dce980 e813a23c60af3b82
ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923
```

# Assurance status
%%%
tag := "blake2-assurance"
%%%

The evidence that the Lean specification is the BLAKE2 of RFC 7693, as of 2026-10-12:

:::table +header
*
  * Evidence
  * Status
*
  * Reference transcription
  * `Hash.BLAKE2.Reference`, for both word sizes and any number of rounds, each definition
    citing its section of RFC 7693 or of the BLAKE2 specification (parameter block).
*
  * Constants
  * The IVs are proved equal to the SHA-2 initial hash values, and each row of `SIGMA` is
    proved a permutation.
*
  * Fast = reference
  * Proved for BLAKE2b and BLAKE2s with every key of at most one block, salt,
    personalisation and output length (`Hash.BLAKE2.blake2bWith_eq`,
    `Hash.BLAKE2.blake2sWith_eq`), and for the EIP-152 compression function with any number of
    rounds (`Hash.BLAKE2.blake2bF_eq`). Streaming equals one-shot, for every way of splitting
    the message and every key of at most one block (`Hash.blake2bInit_eq`,
    `Hash.blake2sInit_eq`). The axiom audit shows only `propext`,
    `Classical.choice` and `Quot.sound`.
*
  * Known-answer tests
  * All 1024 keyed and unkeyed vectors of the BLAKE2 team's `blake2-kat.json` pass, and again
    through the streaming interface in five splitting patterns; EIP-152 test vectors 0–7 pass
    (vector 8, with $`2^{32} − 1` rounds, is skipped as too slow). Kernel-checked examples
    cover RFC 7693 Appendices A and B and EIP-152 vector 5.
*
  * Differential testing
  * Every message length up to 385 bytes with several key lengths, every output length, a
    1 MiB message, random parameters, messages and streaming splits agree with
    `blake2b_simd`/`blake2s_simd` and RustCrypto `blake2`. The precompile agrees with
    `revm-precompile` and the `eip-152` crate on round counts 0–100, random inputs and invalid
    inputs.
*
  * Fuzzing
  * Three `cargo-fuzz` targets (one-shot with parameters, streaming, and the precompile on raw
    inputs); no divergence has been found. The roadmap's budget of $`10^9` executions per
    oracle has not yet been reached.
*
  * Other formal specifications
  * HACL\* and hacspec (F\*), Cryptol and ACL2 specify BLAKE2, and Verifereum (HOL4) the
    EIP-152 $`F` (informational; see `LIT-REVIEW.md`).
*
  * Known deviations
  * Keys longer than one block are outside RFC 7693 and outside the equivalence theorems. The tree-hashing parameters of the BLAKE2
    specification are fixed to sequential mode.
:::

# Security notes
%%%
tag := "blake2-security"
%%%

This section points to the literature; it makes no claims of its own.

- *Design rationale.* The BLAKE2 paper explains the changes from BLAKE, including the reduced
  round counts, and their security margin {citep aumasson2013}[].
- *Cryptanalysis.* Guo et al. analyse BLAKE2's permutation and compression function, with
  impossible-differential and rotational results on reduced rounds; they also show that an
  improper initialization would allow collisions for the full compression function, which the
  IV of the specification avoids {citep guo2014}[].
- *Modes of operation.* Luykx, Mennink and Neves show that the BLAKE2 compression function is
  indifferentiable from a random function in a weakly ideal cipher model, so that none of
  BLAKE2's modes has a generic attack {citep luykx2016}[].
- *No length extension.* The final flag distinguishes the last compression, so a digest cannot
  be extended by appending blocks as for SHA-256.

# References
%%%
tag := "blake2-references"
%%%

- M-J. Saarinen and J-P. Aumasson, *The BLAKE2 Cryptographic Hash and Message Authentication
  Code (MAC)*, RFC 7693, 2015. [doi:10.17487/RFC7693](https://doi.org/10.17487/RFC7693)
- J-P. Aumasson, S. Neves, Z. Wilcox-O'Hearn and C. Winnerlein, *BLAKE2: simpler, smaller, fast
  as MD5*, with the specification at [blake2.net](https://www.blake2.net/blake2.pdf).
- T. Hess, M. Luongo, P. Dyraga and J. Hancock, *EIP-152: Add BLAKE2 compression function F
  precompile*, 2016. [eips.ethereum.org](https://eips.ethereum.org/EIPS/eip-152)
- The BLAKE2 team's test vectors, `blake2-kat.json`, vendored in `HashKAT/vectors/blake2/`.

The papers cited in this chapter are listed in the book's bibliography.
