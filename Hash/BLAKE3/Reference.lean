/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.BLAKE2.Reference
public import Hash.Construction.Tree

/-!
# BLAKE3: reference specification

A transcription of BLAKE3 as specified in [BLAKE3, §2], on 32-bit words (`BitVec 32`) and byte
lists. The input is split into chunks of 1024 bytes, which are the leaves of the binary tree of
`Hash.Construction.Tree`; each chunk is hashed like a BLAKE2s message, and each parent node by a
single compression. The root node is compressed again with an incrementing counter to give
output of any length.

The round function of BLAKE3 is that of BLAKE2s [BLAKE3, §2.2], so the reference reuses
`Hash.BLAKE2.Reference.round` with the parameters of BLAKE2s and the identity message schedule
`SIGMA[0]`; BLAKE3 instead permutes the message words between rounds.

## References

* [BLAKE3] J. O'Connor, J-P. Aumasson, S. Neves, Z. Wilcox-O'Hearn, *BLAKE3: one function, fast
  everywhere*, 2020. <https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf>
-/

@[expose] public section

namespace Hash.BLAKE3

/-- The initialization vector `IV₀ … IV₇`, that of BLAKE2s [BLAKE3, §2.2, Table 1]. -/
def IV : List Nat := BLAKE2.blake2sParams.IV

/-- `MSG_PERMUTATION`: the permutation of the message words applied after each round
[BLAKE3, §2.2, Table 2]. -/
def msgPermutation : List Nat := [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

/-! Domain separation flags [BLAKE3, §2.2, Table 3], named after the specification's
`CHUNK_START`, `CHUNK_END`, `PARENT`, `ROOT`, `KEYED_HASH`, `DERIVE_KEY_CONTEXT` and
`DERIVE_KEY_MATERIAL`. -/

/-- Set on the first block of each chunk. -/
def Flag.chunkStart : Nat := 1
/-- Set on the last block of each chunk. -/
def Flag.chunkEnd : Nat := 2
/-- Set on parent nodes. -/
def Flag.parent : Nat := 4
/-- Set on the root compressions. -/
def Flag.root : Nat := 8
/-- Set on every compression of `keyed_hash`. -/
def Flag.keyedHash : Nat := 16
/-- Set on every compression of the first stage of `derive_key`. -/
def Flag.deriveKeyContext : Nat := 32
/-- Set on every compression of the second stage of `derive_key`. -/
def Flag.deriveKeyMaterial : Nat := 64

/-- `CHUNK_LEN`: the chunk size in bytes [BLAKE3, §2.1]. -/
def chunkLen : Nat := 1024
/-- `BLOCK_LEN`: the block size in bytes [BLAKE3, §2.4]. -/
def blockLen : Nat := 64

namespace Reference

/-- A 32-bit word. -/
abbrev Word := BitVec 32

/-- The little-endian words of a byte string [BLAKE3, §2.4]. -/
def wordsLE (bs : List UInt8) : List Word := BLAKE2.Reference.wordsLE BLAKE2.blake2sParams bs

/-- The little-endian bytes of a list of words. -/
def wordsToBytes (ws : List Word) : List UInt8 :=
  ws.flatMap fun w => (List.range 4).map fun i => (w.toNat / 2 ^ (8 * i)).toUInt8

/-- One round: `G` on the columns, then on the diagonals, with the message words in order. This
is the round of BLAKE2s [BLAKE3, §2.2]. -/
def round (m v : List Word) : List Word := BLAKE2.Reference.round BLAKE2.blake2sParams m v 0

/-- Permute the message words [BLAKE3, §2.2, Table 2]. -/
def permute (m : List Word) : List Word := msgPermutation.map fun i => m.getD i 0

/-- The compression function [BLAKE3, §2.2]: from the chaining value `h`, the message block `m`,
the counter `t`, the number of bytes `b` in the block and the flags `d`, initialise the state,
apply seven rounds with the message words permuted after each, and output sixteen words. The
first eight are the chaining value. -/
def compress (h m : List Word) (t b d : Nat) : List Word :=
  let v := h ++ (IV.take 4).map (BitVec.ofNat 32) ++
    [BitVec.ofNat 32 t, BitVec.ofNat 32 (t / 2 ^ 32), BitVec.ofNat 32 b, BitVec.ofNat 32 d]
  let (v, _) := (List.range 7).foldl (fun (vm : List Word × List Word) _ =>
    (round vm.2 vm.1, permute vm.2)) (v, m)
  (List.range 8).map (fun i => v.getD i 0 ^^^ v.getD (i + 8) 0) ++
    (List.range 8).map (fun i => v.getD (i + 8) 0 ^^^ h.getD i 0)

/-- A node of the tree before its last compression: the inputs of that compression. Its
chaining value is the truncated compression; if it is the root, it is compressed again with the
`Flag.root` flag and counters `0, 1, 2, …` for the output [BLAKE3, §2.6]. -/
structure Output where
  /-- The input chaining value. -/
  cv : List Word
  /-- The message block. -/
  block : List Word
  /-- The counter. -/
  counter : Nat
  /-- The number of bytes in the block. -/
  blockLen : Nat
  /-- The flags. -/
  flags : Nat

/-- The chaining value of a node: the first eight words of its compression [BLAKE3, §2.4,
§2.5]. -/
def Output.chainingValue (o : Output) : List Word :=
  (compress o.cv o.block o.counter o.blockLen o.flags).take 8

/-- The first `d` output bytes of a root node: the full outputs of the root compression with
counters `0, 1, …`, in little-endian order [BLAKE3, §2.6]. -/
def Output.rootBytes (o : Output) (d : Nat) : List UInt8 :=
  ((List.range ((d + 63) / 64)).flatMap fun i =>
    wordsToBytes (compress o.cv o.block i o.blockLen (o.flags ||| Flag.root))).take d

/-- The blocks of a chunk, each of up to 64 bytes; an empty chunk has one empty block. -/
def chunkBlocks (chunk : List UInt8) : List (List UInt8) :=
  if chunk = [] then [[]] else chunks blockLen chunk

/-- The node of chunk `i` [BLAKE3, §2.4]: its blocks are compressed in order from the key
words, with counter `i`, each block zero-padded to 64 bytes and `b` its number of bytes. The
first block sets `Flag.chunkStart` and the last `Flag.chunkEnd`; the last block is returned
uncompressed. -/
def chunkOutput (key : List Word) (flags : Nat) (i : Nat) (chunk : List UInt8) : Output :=
  let bs := chunkBlocks chunk
  let start (j : Nat) := if j = 0 then Flag.chunkStart else 0
  let words (bl : List UInt8) := wordsLE (bl ++ List.replicate (blockLen - bl.length) 0)
  let cv := (List.range (bs.length - 1)).foldl (fun cv j =>
    (compress cv (words (bs.getD j [])) i blockLen (flags ||| start j)).take 8) key
  let last := bs.getD (bs.length - 1) []
  ⟨cv, words last, i, last.length, flags ||| start (bs.length - 1) ||| Flag.chunkEnd⟩

/-- The node of a parent with children's chaining values `l` and `r` [BLAKE3, §2.5]. -/
def parentOutput (key : List Word) (flags : Nat) (l r : List Word) : Output :=
  ⟨key, l ++ r, 0, blockLen, flags ||| Flag.parent⟩

/-- The chunks of the input: 1024 bytes each, the last possibly shorter; an empty input has
one empty chunk [BLAKE3, §2.1]. -/
def inputChunks (input : List UInt8) : List (List UInt8) :=
  if input = [] then [[]] else chunks chunkLen input

/-- BLAKE3 with key words `key` and mode flags `flags`, producing `d` bytes: the root of the
tree over the chunks of the input [BLAKE3, §2.1–2.6]. -/
def hashWith (key : List Word) (flags : Nat) (input : List UInt8) (d : Nat) : List UInt8 :=
  (Tree.root (chunkOutput key flags) (parentOutput key flags) Output.chainingValue
    (inputChunks input) 0).rootBytes d

/-- The `hash` mode [BLAKE3, §2.3]: key words `IV`, no flags. -/
def hash (input : List UInt8) (d : Nat) : List UInt8 :=
  hashWith (IV.map (BitVec.ofNat 32)) 0 input d

/-- The `keyed_hash` mode [BLAKE3, §2.3]: the key words are the 32-byte key in little-endian
order, and `Flag.keyedHash` is set. -/
def keyedHash (key : List UInt8) (input : List UInt8) (d : Nat) : List UInt8 :=
  hashWith (wordsLE key) Flag.keyedHash input d

/-- The `derive_key` mode [BLAKE3, §2.3]: hash the context string with `Flag.deriveKeyContext`,
then the key material with the first 32 bytes of that as the key and `Flag.deriveKeyMaterial`. -/
def deriveKey (context material : List UInt8) (d : Nat) : List UInt8 :=
  let contextKey := hashWith (IV.map (BitVec.ofNat 32)) Flag.deriveKeyContext context 32
  hashWith (wordsLE contextKey) Flag.deriveKeyMaterial material d

end Reference

end Hash.BLAKE3
