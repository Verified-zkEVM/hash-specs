/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

/-!
# Byte strings and machine words

Helpers for the fast specifications: hexadecimal encoding, and big- and little-endian loads and
stores of `UInt32` and `UInt64` words in a `ByteArray`. This file is Mathlib-free.
-/

@[expose] public section

namespace Hash

/-! ### Hexadecimal -/

/-- The lowercase hexadecimal digit for a value below 16. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The value of a hexadecimal digit, accepting both cases. -/
def hexValue? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

/-- Lowercase hexadecimal encoding of a list of bytes. -/
def bytesToHex (bs : List UInt8) : String :=
  String.ofList <| bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- Decode a hexadecimal string of even length. -/
def hexToBytes? (s : String) : Option (List UInt8) :=
  go s.toList
where
  /-- Decode a list of hexadecimal digits, two at a time. -/
  go : List Char → Option (List UInt8)
    | [] => some []
    | [_] => none
    | hi :: lo :: rest => do
      let h ← hexValue? hi
      let l ← hexValue? lo
      let tl ← go rest
      pure ((16 * h + l).toUInt8 :: tl)

/-- Lowercase hexadecimal encoding of a byte array. -/
def ByteArray.toHex (b : ByteArray) : String :=
  bytesToHex b.toList

/-- Decode a hexadecimal string into a byte array. -/
def ByteArray.ofHex? (s : String) : Option ByteArray :=
  (hexToBytes? s).map fun l => ⟨l.toArray⟩

/-! ### Rotations -/

/-- Rotate a 32-bit word right by `n` places (`0 < n < 32`). -/
@[inline] def UInt32.rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Rotate a 64-bit word right by `n` places (`0 < n < 64`). -/
@[inline] def UInt64.rotr (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- Rotate a 64-bit word left by `n` places (`0 < n < 64`). -/
@[inline] def UInt64.rotl (x : UInt64) (n : UInt64) : UInt64 :=
  (x <<< n) ||| (x >>> (64 - n))

/-! ### Loads and stores -/

/-- The big-endian 32-bit word at byte offset `i` of `a` (out-of-range bytes read as zero). -/
@[inline] def ByteArray.getUInt32BE (a : ByteArray) (i : Nat) : UInt32 :=
  (a.get! i).toUInt32 <<< 24 ||| (a.get! (i + 1)).toUInt32 <<< 16 |||
    (a.get! (i + 2)).toUInt32 <<< 8 ||| (a.get! (i + 3)).toUInt32

/-- The big-endian 64-bit word at byte offset `i` of `a` (out-of-range bytes read as zero). -/
@[inline] def ByteArray.getUInt64BE (a : ByteArray) (i : Nat) : UInt64 :=
  (a.get! i).toUInt64 <<< 56 ||| (a.get! (i + 1)).toUInt64 <<< 48 |||
    (a.get! (i + 2)).toUInt64 <<< 40 ||| (a.get! (i + 3)).toUInt64 <<< 32 |||
    (a.get! (i + 4)).toUInt64 <<< 24 ||| (a.get! (i + 5)).toUInt64 <<< 16 |||
    (a.get! (i + 6)).toUInt64 <<< 8 ||| (a.get! (i + 7)).toUInt64

/-- The little-endian 32-bit word at byte offset `i` of `a` (out-of-range bytes read as zero). -/
@[inline] def ByteArray.getUInt32LE (a : ByteArray) (i : Nat) : UInt32 :=
  (a.get! i).toUInt32 ||| (a.get! (i + 1)).toUInt32 <<< 8 |||
    (a.get! (i + 2)).toUInt32 <<< 16 ||| (a.get! (i + 3)).toUInt32 <<< 24

/-- The little-endian 64-bit word at byte offset `i` of `a` (out-of-range bytes read as zero). -/
@[inline] def ByteArray.getUInt64LE (a : ByteArray) (i : Nat) : UInt64 :=
  (a.get! i).toUInt64 ||| (a.get! (i + 1)).toUInt64 <<< 8 |||
    (a.get! (i + 2)).toUInt64 <<< 16 ||| (a.get! (i + 3)).toUInt64 <<< 24 |||
    (a.get! (i + 4)).toUInt64 <<< 32 ||| (a.get! (i + 5)).toUInt64 <<< 40 |||
    (a.get! (i + 6)).toUInt64 <<< 48 ||| (a.get! (i + 7)).toUInt64 <<< 56

/-- Append a 32-bit word in big-endian order. -/
@[inline] def ByteArray.pushUInt32BE (a : ByteArray) (x : UInt32) : ByteArray :=
  a.push (x >>> 24).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 8).toUInt8 |>.push x.toUInt8

/-- Append a 64-bit word in big-endian order. -/
@[inline] def ByteArray.pushUInt64BE (a : ByteArray) (x : UInt64) : ByteArray :=
  a.push (x >>> 56).toUInt8 |>.push (x >>> 48).toUInt8 |>.push (x >>> 40).toUInt8
    |>.push (x >>> 32).toUInt8 |>.push (x >>> 24).toUInt8 |>.push (x >>> 16).toUInt8
    |>.push (x >>> 8).toUInt8 |>.push x.toUInt8

/-- Append a 32-bit word in little-endian order. -/
@[inline] def ByteArray.pushUInt32LE (a : ByteArray) (x : UInt32) : ByteArray :=
  a.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8

/-- Append a 64-bit word in little-endian order. -/
@[inline] def ByteArray.pushUInt64LE (a : ByteArray) (x : UInt64) : ByteArray :=
  a.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8
    |>.push (x >>> 24).toUInt8 |>.push (x >>> 32).toUInt8 |>.push (x >>> 40).toUInt8
    |>.push (x >>> 48).toUInt8 |>.push (x >>> 56).toUInt8

/-- `n` zero bytes. -/
def ByteArray.zeros (n : Nat) : ByteArray :=
  ⟨Array.replicate n 0⟩

end Hash
