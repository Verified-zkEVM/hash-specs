/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.BLAKE3.Reference
public import Hash.BLAKE2.Fast

/-!
# BLAKE3: fast specification

An executable BLAKE3 over byte arrays and `UInt32` arrays, following the reference
(`Hash.BLAKE3.Reference`) step by step. It reuses the BLAKE2s round of `Hash.BLAKE2.Fast`, and
the tree of `Hash.Construction.Tree` over the chunks of the input.

`Hash.BLAKE3.Equiv` proves that it computes the reference, and `Hash.BLAKE3.Stream` gives an
incremental interface proved equal to it.
-/

@[expose] public section

namespace Hash.BLAKE3.Fast

open BLAKE2.Fast BLAKE2.Fast.Word

/-- Permute the message words, as in the reference. -/
def permute (m : Array UInt32) : Array UInt32 := (MSG_PERMUTATION.map fun i => get m i).toArray

/-- The compression function, as in the reference. -/
def compress (h m : Array UInt32) (t b d : Nat) : Array UInt32 :=
  let v := h ++ ((IV.take 4).map ofNat).toArray ++
    #[ofNat t, ofNat (t / 2 ^ 32), ofNat b, ofNat d]
  let (v, _) := (List.range 7).foldl (fun (vm : Array UInt32 × Array UInt32) _ =>
    (round BLAKE2.blake2sParams vm.2 vm.1 0, permute vm.2)) (v, m)
  ((List.range 8).map (fun i => xor (get v i) (get v (i + 8))) ++
    (List.range 8).map (fun i => xor (get v (i + 8)) (get h i))).toArray

/-- A node before its last compression, as in the reference. -/
structure Output where
  /-- The input chaining value. -/
  cv : Array UInt32
  /-- The message block. -/
  block : Array UInt32
  /-- The counter. -/
  counter : Nat
  /-- The number of bytes in the block. -/
  blockLen : Nat
  /-- The flags. -/
  flags : Nat

/-- The chaining value of a node. -/
def Output.chainingValue (o : Output) : Array UInt32 :=
  (compress o.cv o.block o.counter o.blockLen o.flags).extract 0 8

/-- The first `d` output bytes of a root node. -/
def Output.rootBytes (o : Output) (d : Nat) : ByteArray :=
  ((List.range ((d + 63) / 64)).foldl (fun acc i =>
    (compress o.cv o.block i o.blockLen (o.flags ||| ROOT)).foldl pushLE acc)
    ByteArray.empty).extract 0 d

/-- The node of chunk `i`, as in the reference, on a single zero-padded copy of the chunk. -/
def chunkOutput (key : Array UInt32) (flags : Nat) (i : Nat) (chunk : ByteArray) : Output :=
  let nb := if chunk.size = 0 then 1 else (chunk.size + BLOCK_LEN - 1) / BLOCK_LEN
  let p := chunk ++ ByteArray.zeros (nb * BLOCK_LEN - chunk.size)
  let start (j : Nat) := if j = 0 then CHUNK_START else 0
  let cv := (List.range (nb - 1)).foldl (fun cv j =>
    (compress cv (block BLAKE2.blake2sParams p (j * BLOCK_LEN)) i BLOCK_LEN
      (flags ||| start j)).extract 0 8) key
  ⟨cv, block BLAKE2.blake2sParams p ((nb - 1) * BLOCK_LEN), i,
    chunk.size - (nb - 1) * BLOCK_LEN, flags ||| start (nb - 1) ||| CHUNK_END⟩

/-- The node of a parent, as in the reference. -/
def parentOutput (key : Array UInt32) (flags : Nat) (l r : Array UInt32) : Output :=
  ⟨key, l ++ r, 0, BLOCK_LEN, flags ||| PARENT⟩

/-- The chunks of the input, as in the reference. -/
def inputChunks (input : ByteArray) : List ByteArray :=
  let n := if input.size = 0 then 1 else (input.size + CHUNK_LEN - 1) / CHUNK_LEN
  (List.range n).map fun j => input.extract (j * CHUNK_LEN) ((j + 1) * CHUNK_LEN)

/-- The root node of the tree over the chunks. -/
def rootOutput (key : Array UInt32) (flags : Nat) (input : ByteArray) : Output :=
  Tree.root (chunkOutput key flags) (parentOutput key flags) Output.chainingValue
    (inputChunks input) 0

/-- BLAKE3 with key words `key` and mode flags `flags`, producing `d` bytes. -/
def hashWith (key : Array UInt32) (flags : Nat) (input : ByteArray) (d : Nat) : ByteArray :=
  (rootOutput key flags input).rootBytes d

/-- The key words of the `hash` mode: the IV. -/
def ivWords : Array UInt32 := (IV.map ofNat).toArray

/-- The eight little-endian words of a 32-byte key. -/
def keyWords (key : ByteArray) : Array UInt32 :=
  ((List.range 8).map fun j => loadLE key (4 * j)).toArray

end Hash.BLAKE3.Fast
