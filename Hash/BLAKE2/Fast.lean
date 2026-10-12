/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.BLAKE2.Reference
public import Hash.Prelude.Bytes

/-!
# BLAKE2: fast specification

An executable BLAKE2 over byte arrays and machine words, following the reference
(`Hash.BLAKE2.Reference`) step by step on `UInt64` (BLAKE2b) or `UInt32` (BLAKE2s) arrays. It is
generic over the word type through the `Word` class.

`Hash.BLAKE2.Equiv` proves that it computes the reference.
-/

@[expose] public section

namespace Hash.BLAKE2.Fast

/-- The machine-word operations used by BLAKE2. -/
class Word (α : Type) where
  /-- The zero word. -/
  zero : α
  /-- The word with the given value modulo `2^w`. -/
  ofNat : Nat → α
  /-- Addition modulo `2^w`. -/
  add : α → α → α
  /-- Bitwise exclusive or. -/
  xor : α → α → α
  /-- Bitwise complement. -/
  not : α → α
  /-- Rotate right by the given amount (less than `w`). -/
  rotr : α → Nat → α
  /-- The little-endian word at a byte offset of a byte array. -/
  loadLE : ByteArray → Nat → α
  /-- Append a word to a byte array in little-endian order. -/
  pushLE : ByteArray → α → ByteArray

instance : Word UInt64 where
  zero := 0
  ofNat := UInt64.ofNat
  add := (· + ·)
  xor := (· ^^^ ·)
  not := (~~~ ·)
  rotr x n := UInt64.rotr x n.toUInt64
  loadLE := ByteArray.getUInt64LE
  pushLE := ByteArray.pushUInt64LE

instance : Word UInt32 where
  zero := 0
  ofNat := UInt32.ofNat
  add := (· + ·)
  xor := (· ^^^ ·)
  not := (~~~ ·)
  rotr x n := UInt32.rotr x n.toUInt32
  loadLE := ByteArray.getUInt32LE
  pushLE := ByteArray.pushUInt32LE

open Word

variable {α : Type} [Word α]

/-- Word `i` of an array, or zero out of range. -/
@[inline] def get (v : Array α) (i : Nat) : α := v.getD i zero

/-- The mixing function `G`, as in the reference. -/
@[specialize] def G (P : Params) (v : Array α) (a b c d : Nat) (x y : α) : Array α :=
  let (R1, R2, R3, R4) := P.R
  let v := v.set! a (add (add (get v a) (get v b)) x)
  let v := v.set! d (rotr (xor (get v d) (get v a)) R1)
  let v := v.set! c (add (get v c) (get v d))
  let v := v.set! b (rotr (xor (get v b) (get v c)) R2)
  let v := v.set! a (add (add (get v a) (get v b)) y)
  let v := v.set! d (rotr (xor (get v d) (get v a)) R3)
  let v := v.set! c (add (get v c) (get v d))
  v.set! b (rotr (xor (get v b) (get v c)) R4)

/-- One round, as in the reference. -/
@[specialize] def round (P : Params) (m : Array α) (v : Array α) (i : Nat) : Array α :=
  let s := SIGMA.getD (i % 10) []
  let x (j : Nat) := get m (s.getD j 0)
  let v := G P v 0 4  8 12 (x 0) (x 1)
  let v := G P v 1 5  9 13 (x 2) (x 3)
  let v := G P v 2 6 10 14 (x 4) (x 5)
  let v := G P v 3 7 11 15 (x 6) (x 7)
  let v := G P v 0 5 10 15 (x 8) (x 9)
  let v := G P v 1 6 11 12 (x 10) (x 11)
  let v := G P v 2 7  8 13 (x 12) (x 13)
  G P v 3 4  9 14 (x 14) (x 15)

/-- The compression function `F` with `rounds` rounds, as in the reference. -/
@[specialize] def F (P : Params) (rounds : Nat) (h m : Array α) (t : Nat) (f : Bool) :
    Array α :=
  let v := h ++ (P.IV.map ofNat).toArray
  let v := v.set! 12 (xor (get v 12) (ofNat t))
  let v := v.set! 13 (xor (get v 13) (ofNat (t / 2 ^ P.w)))
  let v := if f then v.set! 14 (not (get v 14)) else v
  let v := (List.range rounds).foldl (round P m) v
  ((List.range 8).map fun i => xor (xor (get h i) (get v i)) (get v (i + 8))).toArray

/-- The sixteen message words of the block at byte offset `off`. -/
@[specialize] def block (P : Params) (p : ByteArray) (off : Nat) : Array α :=
  ((List.range 16).map fun j => loadLE p (off + j * (P.w / 8))).toArray

/-- The parameter block, as in the reference. -/
def paramBlock (P : Params) (nn kk : Nat) (salt personal : ByteArray) : ByteArray :=
  ⟨(Reference.paramBlock P nn kk salt.data.toList personal.data.toList).toArray⟩

/-- BLAKE2 with words of type `α`: as in the reference, on a single zero-padded copy of the key
block and the message. -/
@[specialize] def hashWith (α : Type) [Word α] (P : Params) (key salt personal : ByteArray)
    (nn : Nat) (msg : ByteArray) : ByteArray :=
  let bb := P.blockBytes
  let kk := key.size
  let ll := msg.size
  let pb := paramBlock P nn kk salt personal
  let h : Array α := ((List.range 8).map fun i =>
    xor (ofNat (P.IV.getD i 0)) (loadLE pb (i * (P.w / 8)))).toArray
  let keyBlock := if kk = 0 then ByteArray.empty else key ++ ByteArray.zeros (bb - kk)
  let p := keyBlock ++ msg ++ ByteArray.zeros ((bb - ll % bb) % bb)
  let p := if p.size = 0 then ByteArray.zeros bb else p
  let dd := p.size / bb
  let h := (List.range (dd - 1)).foldl
    (fun h i => F P P.rounds h (block P p (i * bb)) ((i + 1) * bb) false) h
  let t := if kk = 0 then ll else ll + bb
  let h := F P P.rounds h (block P p ((dd - 1) * bb)) t true
  (h.foldl pushLE ByteArray.empty).extract 0 nn

end Hash.BLAKE2.Fast
