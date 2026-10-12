/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import VersoManual
import Hash.BLAKE3.API
import Hash.BLAKE2.Constants
import HashDocs.Bibliography

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open HashDocs.Bib

set_option pp.rawOnError true

#doc (Manual) "BLAKE3" =>
%%%
tag := "blake3"
%%%

BLAKE3 is the hash function of *BLAKE3: one function, fast everywhere* by Jack O'Connor,
Jean-Philippe Aumasson, Samuel Neves and Zooko Wilcox-O'Hearn
([specification](https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf)). This
chapter explains the specification alongside its Lean specification, `Hash.BLAKE3`. Section
numbers in parentheses refer to the BLAKE3 specification.

# Overview and history
%%%
tag := "blake3-overview"
%%%

BLAKE3 was published in 2020. It keeps the compression function of BLAKE2s
{citep aumasson2013}[], reduced from 10 to 7 rounds, and replaces BLAKE2's sequential mode with
a binary tree of 1024-byte chunks, so that long inputs can be hashed in parallel and with SIMD.
A single function provides hashing, keyed hashing (a MAC or PRF), key derivation, and output of
any length (§2.3, §2.6). BLAKE3 has no NIST or IETF standard; the specification and the BLAKE3
team's reference implementation define it. It is used for content addressing and integrity
checking, and the `clean` project specifies BLAKE3 circuits for zero-knowledge virtual
machines.

:::table +header
*
  * Mode
  * Key words
  * Flags
  * Lean
*
  * `hash`
  * the IV
  * none
  * `Hash.blake3`, `Hash.blake3Xof`
*
  * `keyed_hash`
  * the 32-byte key
  * `KEYED_HASH`
  * `Hash.blake3Keyed`
*
  * `derive_key`
  * the hash of the context string
  * `DERIVE_KEY_CONTEXT`, then `DERIVE_KEY_MATERIAL`
  * `Hash.blake3DeriveKey`
:::

The *reference* specification (`Hash.BLAKE3.Reference`) transcribes §2 on 32-bit bit vectors
and byte lists. It reuses the BLAKE2s round of `Hash.BLAKE2.Reference`, as the specification
does, and the generic tree of `Hash.Construction.Tree`. The *fast* specification
(`Hash.BLAKE3.Fast`) works on byte arrays and `UInt32` arrays, and has a streaming interface.
The two are proved equal, and streaming is proved equal to one-shot hashing (see
{ref "blake3-assurance"}[Assurance status]).

# Notation and data model
%%%
tag := "blake3-data-model"
%%%

Like BLAKE2s, BLAKE3 reads bytes as 32-bit words in little-endian order and writes its output
the same way (see the BLAKE2 chapter). The input is split into *chunks* of 1024 bytes, the last
possibly shorter, and each chunk into *blocks* of 64 bytes, the last zero-padded; an empty input
is one empty chunk with one empty block (§2.1, §2.4).

{docstring Hash.BLAKE3.Reference.inputChunks}

{docstring Hash.BLAKE3.Reference.chunkBlocks}

Every compression takes a set of *domain separation flags*, which record what the compression
is for (§2.2, Table 3): the first and last block of a chunk, a parent node, the root, and the
mode.

{docstring Hash.BLAKE3.Flag.chunkStart}

{docstring Hash.BLAKE3.Flag.root}

# State and primitives
%%%
tag := "blake3-state"
%%%

The compression function initialises a 4×4 state from the chaining value, four words of the IV,
the 64-bit counter, the number of bytes in the block, and the flags. It applies seven rounds of
the BLAKE2s round, permuting the message words between rounds, and outputs sixteen words: the
first eight are the next chaining value, and all sixteen are used for the root's output (§2.2).

![The BLAKE3 compression function](../static/blake3-compress.svg)

{docstring Hash.BLAKE3.Reference.compress}

# The round function
%%%
tag := "blake3-round"
%%%

The round is that of BLAKE2s: $`G` on the four columns, then on the four diagonals, with
rotations $`(16, 12, 8, 7)` (§2.2; see the BLAKE2 chapter for $`G`). BLAKE3 takes the message
words in order and permutes them after each round, where BLAKE2 indexes them through `SIGMA`:

{docstring Hash.BLAKE3.Reference.round}

{docstring Hash.BLAKE3.msgPermutation}

{docstring Hash.BLAKE3.Reference.permute}

# Mode of operation
%%%
tag := "blake3-mode"
%%%

Each chunk is hashed like a BLAKE2s message: its blocks are compressed in order, starting from
the key words, with the chunk index as the counter (§2.4).

![A BLAKE3 chunk](../static/blake3-chunk.svg)

{docstring Hash.BLAKE3.Reference.chunkOutput}

The chunks are the leaves of a binary tree whose left subtrees are complete and at least as big
as their right siblings (§2.1). A parent node compresses the two children's chaining values as
one block (§2.5).

![BLAKE3 tree shapes](../static/blake3-tree.svg)

{docstring Hash.Tree.leftLeaves}

{docstring Hash.Tree.root}

{docstring Hash.BLAKE3.Reference.parentOutput}

The root is compressed again with the `ROOT` flag and the counter $`0, 1, 2, …`, giving 64 bytes
of output each time, so the output can be as long as needed (§2.6):

![BLAKE3 extendable output](../static/blake3-xof.svg)

{docstring Hash.BLAKE3.Reference.Output.rootBytes}

{docstring Hash.BLAKE3.Reference.hashWith}

{docstring Hash.BLAKE3.Reference.deriveKey}

## Incremental hashing
%%%
tag := "blake3-stream"
%%%

An incremental implementation cannot know which chunk is last, so it keeps a stack of the
chaining values of complete subtrees and merges them as chunks arrive (§5.1.2). After $`k`
chunks the stack has one entry per 1-bit of $`k`, and adding a chunk merges one entry per
trailing 1-bit:

![The chaining-value stack](../static/blake3-stack.svg)

{docstring Hash.Tree.merge}

{docstring Hash.Tree.finish}

The library proves that this computes the tree, generically (`Hash.Tree.finish_pushAll`), and
that the streaming interface of `Hash.BLAKE3.Fast.State` gives the one-shot output for every
split of the input: `Hash.blake3Init_eq` states that folding `Hash.BLAKE3.Fast.State.update`
over pieces `ms` from `Hash.blake3Init`, then finalizing with output length `d`, gives
`Hash.blake3Xof` of the concatenation of `ms`, and similarly for the other two modes.

# Parameters and constants
%%%
tag := "blake3-constants"
%%%

BLAKE3 has few constants of its own. The IV is that of BLAKE2s, and so the SHA-256 initial hash
value (§2.2, Table 1):

```lean
open Hash in
example : BLAKE3.IV = SHA2.initialHash256 :=
  BLAKE2.blake2s_IV
```

The message permutation of Table 2 replaces BLAKE2's ten `SIGMA` rows; the flags are the
powers of 2 from $`2^0` to $`2^6` (Table 3); chunks are 1024 bytes and blocks 64 bytes. The
specification explains the chunk size, the key schedule and the round count (§7, §4.4).

# Worked example
%%%
tag := "blake3-example"
%%%

We trace BLAKE3 on the 1025-byte input of the official test vectors, the bytes
$`0, 1, …, 250` repeated. It has two chunks, so the tree is one parent node over two chunks.
The values are computed by the fast specification when this book is built, and the build fails
if any differs from the text shown. The final output agrees with the official vector.

```lean
open Hash Hash.BLAKE3 Hash.BLAKE3.Fast

/-- A word as eight hexadecimal digits. -/
def b3hex (x : UInt32) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  String.ofList (List.replicate (8 - s.length) '0')
    ++ s

/-- Print words separated by spaces. -/
def b3print (ws : Array UInt32) : IO Unit :=
  IO.println (" ".intercalate (ws.toList.map b3hex))

def b3input : ByteArray :=
  ⟨((List.range 1025).map fun i =>
    (i % 251).toUInt8).toArray⟩
```

The input splits into a full chunk and a one-byte chunk:

```lean (name := b3chunks)
def b3chunks : List ByteArray := inputChunks b3input

#eval IO.println (b3chunks.map ByteArray.size)
```

```leanOutput b3chunks
[1024, 1]
```

The chaining values of the two chunks, with counters 0 and 1:

```lean (name := b3cvs)
def b3c0 : Array UInt32 :=
  (chunkOutput ivWords 0 0
    (b3chunks.getD 0 .empty)).chainingValue

def b3c1 : Array UInt32 :=
  (chunkOutput ivWords 0 1
    (b3chunks.getD 1 .empty)).chainingValue

#eval do
  b3print b3c0
  b3print b3c1
```

```leanOutput b3cvs
44659e5c d193e311 10c7bef4 56bcd5cc 7d17ab69 b60e0a61 e9fefc91 b1e8b42f
8a8e002f 8c717969 d72f2f0c fee7b6de 8e3d1a4c 609c1390 b63e16cc 1184ad10
```

The root is the parent of the two chunks; its output is the hash:

```lean (name := b3root)
#eval do
  let root := parentOutput ivWords 0 b3c0 b3c1
  IO.println (root.rootBytes 32).toHex
  IO.println (blake3 b3input).toHex
```

```leanOutput b3root
d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444
d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444
```

# Assurance status
%%%
tag := "blake3-assurance"
%%%

The evidence that the Lean specification is the BLAKE3 of its specification, as of
2026-10-12:

:::table +header
*
  * Evidence
  * Status
*
  * Reference transcription
  * `Hash.BLAKE3.Reference` and `Hash.Construction.Tree`, each definition citing its section of
    the specification.
*
  * Constants
  * The IV is the BLAKE2s IV, proved equal to the SHA-256 initial hash value.
*
  * Fast = reference
  * Proved for all three modes with every output length (`Hash.BLAKE3.blake3Xof_eq`,
    `Hash.BLAKE3.blake3Keyed_eq` for 32-byte keys, `Hash.BLAKE3.blake3DeriveKey_eq`). The
    axiom audit shows only `propext`, `Classical.choice` and `Quot.sound`.
*
  * Streaming = one-shot
  * Proved for every key, mode, output length and split of the input
    (`Hash.BLAKE3.Fast.State.finalize_updates`), from the generic theorem that the
    chaining-value stack computes the tree (`Hash.Tree.finish_pushAll`). Shorter outputs are
    proved to be prefixes of longer ones (`Hash.BLAKE3.blake3Xof_prefix`).
*
  * Known-answer tests
  * All 35 cases of the BLAKE3 team's `test_vectors.json` pass in all three modes, at the full
    131 bytes and at 32 bytes, one-shot and through the streaming interface in eight splitting
    patterns (`lake exe hash-kat`). Kernel-checked examples cover the three modes on the empty
    input and `hash` on 1 and 65 bytes.
*
  * Differential testing
  * Every input length up to 2049 bytes and a sample up to 16 KiB, output lengths around the
    64-byte blocks, a 1 MiB input, random inputs, keys, contexts and streaming splits agree with
    the `blake3` crate and the BLAKE3 team's reference implementation.
*
  * Fuzzing
  * Two `cargo-fuzz` targets (all modes one-shot, and streaming); no divergence has been found.
    The roadmap's budget of $`10^9` executions per oracle has not yet been reached.
*
  * Other formal specifications
  * `clean` (Verified-zkEVM) has a Lean 4 specification of BLAKE3 with circuit gadgets
    (informational; see `LIT-REVIEW.md`).
*
  * Known deviations
  * `Hash.blake3DeriveKey` takes the context string as bytes; the specification intends a
    hard-coded string, which the caller encodes as UTF-8.
:::

# Security notes
%%%
tag := "blake3-security"
%%%

This section points to the literature; it makes no claims of its own.

- *Security goals.* BLAKE3 targets 128-bit security against preimage, second-preimage,
  collision and differentiability attacks, with 256-bit keys (§4.1).
- *Mode of operation.* The specification argues that the tree mode is sound in the sense of
  Daemen et al.: subtree-free, thanks to the `ROOT` flag, radically decodable and message
  complete; together with the indifferentiability of the truncated compression function, this
  gives the bound of §4.3. The untruncated root output is not indifferentiable in the same way,
  and the specification discusses the role of the feed-forward (§4.2, §4.3).
- *Round count.* The reduction from 10 to 7 rounds rests on the cryptanalysis of BLAKE and
  BLAKE2 summarised in §4.4, including that of Guo et al. {citep guo2014}[].
- *No length extension.* Only the root sets the `ROOT` flag, so a hash cannot be extended into
  the hash of a longer input (§4.3).

# References
%%%
tag := "blake3-references"
%%%

- J. O'Connor, J-P. Aumasson, S. Neves and Z. Wilcox-O'Hearn, *BLAKE3: one function, fast
  everywhere*, 2020.
  [github.com/BLAKE3-team/BLAKE3-specs](https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf)
- The BLAKE3 team's test vectors, `test_vectors.json`, vendored in `HashKAT/vectors/blake3/`,
  and reference implementation, vendored in `harness/blake3-reference/`.

The papers cited in this chapter are listed in the book's bibliography.
