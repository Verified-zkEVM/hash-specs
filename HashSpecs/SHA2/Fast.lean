/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import HashSpecs.Prelude.Bytes
public import HashSpecs.SHA2.Reference

/-!
# SHA-2: fast specification

An executable SHA-2 over byte arrays and machine words. It follows the structure of the reference
specification (`HashSpecs.SHA2.Reference`) step by step, but works on `ByteArray` messages and
`UInt32`/`UInt64` words instead of bit strings and `BitVec w`. It is generic over the word type
through the `Word` class, and specialised by the compiler for `UInt32` and `UInt64`.

`HashSpecs.SHA2.Equiv` proves that, on byte-aligned messages, this function computes exactly the
reference specification.
-/

@[expose] public section

namespace HashSpecs.SHA2.Fast

/-- The machine-word operations used by SHA-2. -/
class Word (α : Type) where
  /-- The zero word. -/
  zero : α
  /-- The word with the given value modulo `2^w`. -/
  ofNat : Nat → α
  /-- Addition modulo `2^w`. -/
  add : α → α → α
  /-- Bitwise exclusive or. -/
  xor : α → α → α
  /-- Bitwise and. -/
  and : α → α → α
  /-- Bitwise complement. -/
  not : α → α
  /-- Rotate right by the given amount (between 0 and `w − 1`). -/
  rotr : α → Nat → α
  /-- Shift right by the given amount (between 0 and `w − 1`). -/
  shr : α → Nat → α
  /-- The big-endian word at a byte offset of a byte array. -/
  loadBE : ByteArray → Nat → α
  /-- Append a word to a byte array in big-endian order. -/
  pushBE : ByteArray → α → ByteArray

instance : Word UInt32 where
  zero := 0
  ofNat := UInt32.ofNat
  add := (· + ·)
  xor := (· ^^^ ·)
  and := (· &&& ·)
  not := (~~~ ·)
  rotr x n := UInt32.rotr x n.toUInt32
  shr x n := x >>> n.toUInt32
  loadBE := ByteArray.getUInt32BE
  pushBE := ByteArray.pushUInt32BE

instance : Word UInt64 where
  zero := 0
  ofNat := UInt64.ofNat
  add := (· + ·)
  xor := (· ^^^ ·)
  and := (· &&& ·)
  not := (~~~ ·)
  rotr x n := UInt64.rotr x n.toUInt64
  shr x n := x >>> n.toUInt64
  loadBE := ByteArray.getUInt64BE
  pushBE := ByteArray.pushUInt64BE

open Word
open Reference (Vars)

variable {α : Type} [Word α]

/-- `Ch`, as in the reference. -/
@[specialize, inline] def Ch (x y z : α) : α := xor (and x y) (and (not x) z)

/-- `Maj`, as in the reference. -/
@[specialize, inline] def Maj (x y z : α) : α := xor (xor (and x y) (and x z)) (and y z)

/-- `Σ`, as in the reference. -/
@[specialize, inline] def bigSigma (a : Amounts) (x : α) : α :=
  xor (xor (rotr x a.r₁) (rotr x a.r₂)) (rotr x a.r₃)

/-- `σ`, as in the reference. -/
@[specialize, inline] def smallSigma (a : Amounts) (x : α) : α :=
  xor (xor (rotr x a.r₁) (rotr x a.r₂)) (shr x a.r₃)

/-- `n` bytes holding `v` in big-endian order (only the low `8n` bits of `v` are kept). -/
def natToBytesBE (n v : Nat) : ByteArray :=
  ⟨((List.range n).reverse.map fun i => (v >>> (8 * i)).toUInt8).toArray⟩

/-- Byte-level padding: the message, the byte `0x80`, zero bytes, and the bit length as a
big-endian number of `lengthBits / 8` bytes. On byte-aligned messages this is exactly the
reference padding. -/
def pad (P : Params) (m : ByteArray) : ByteArray :=
  let blockBytes := P.blockBits / 8
  let lengthBytes := P.lengthBits / 8
  let zeros := (blockBytes - (m.size + 1 + lengthBytes) % blockBytes) % blockBytes
  m.push 0x80 ++ ByteArray.zeros zeros ++ natToBytesBE lengthBytes (8 * m.size)

/-- The message schedule of the block at byte offset `off` of `p`. -/
@[specialize] def schedule (P : Params) (p : ByteArray) (off : Nat) : Array α :=
  (List.range P.rounds).foldl (init := Array.emptyWithCapacity P.rounds) fun W t =>
    W.push (if t < 16 then loadBE p (off + t * (P.w / 8))
      else add (add (add (smallSigma P.smallSigma1 (W.getD (t - 2) zero)) (W.getD (t - 7) zero))
        (smallSigma P.smallSigma0 (W.getD (t - 15) zero))) (W.getD (t - 16) zero))

/-- One round of the compression function. -/
@[specialize] def round (P : Params) (K W : Array α) (v : Vars α) (t : Nat) : Vars α :=
  let T₁ := add (add (add (add v.h (bigSigma P.bigSigma1 v.e)) (Ch v.e v.f v.g)) (K.getD t zero))
    (W.getD t zero)
  let T₂ := add (bigSigma P.bigSigma0 v.a) (Maj v.a v.b v.c)
  { h := v.g, g := v.f, f := v.e, e := add v.d T₁, d := v.c, c := v.b, b := v.a, a := add T₁ T₂ }

/-- Process the block at byte offset `off` of `p`, updating the hash value `H`. -/
@[specialize] def compress (P : Params) (K : Array α) (H : Array α) (p : ByteArray) (off : Nat) :
    Array α :=
  let W := schedule P p off
  let v₀ : Vars α := ⟨H.getD 0 zero, H.getD 1 zero, H.getD 2 zero, H.getD 3 zero,
    H.getD 4 zero, H.getD 5 zero, H.getD 6 zero, H.getD 7 zero⟩
  let v := (List.range P.rounds).foldl (round P K W) v₀
  #[add v.a (H.getD 0 zero), add v.b (H.getD 1 zero), add v.c (H.getD 2 zero),
    add v.d (H.getD 3 zero), add v.e (H.getD 4 zero), add v.f (H.getD 5 zero),
    add v.g (H.getD 6 zero), add v.h (H.getD 7 zero)]

/-- The SHA-2 hash of a byte array, with words of type `α`. The digest length `digestBits` must
be a multiple of 8. -/
@[specialize] def hashWith (α : Type) [Word α] (P : Params) (m : ByteArray) : ByteArray :=
  let blockBytes := P.blockBits / 8
  let p := pad P m
  let K : Array α := (P.K.map ofNat).toArray
  let H₀ : Array α := (P.H0.map ofNat).toArray
  let H := (List.range (p.size / blockBytes)).foldl
    (fun H i => compress P K H p (i * blockBytes)) H₀
  (H.foldl pushBE ByteArray.empty).extract 0 (P.digestBits / 8)

end HashSpecs.SHA2.Fast
