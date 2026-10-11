/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

/-!
# Bit strings

Hash standards describe their inputs as *bit strings*. We model a bit string as a `List Bool`.
Two conventions for converting between bytes and bits appear in the standards covered here:

* **Most significant bit first** (`bytesToBitsMSB`), used by FIPS 180-4 (SHA-2): "the left-most
  bit" of a word or byte is its most significant bit [FIPS 180-4, §3.1].
* **Least significant bit first** (`bytesToBitsLSB`), used by FIPS 202 (SHA-3): the function
  `h2b` converts each byte into eight bits starting from the least significant one
  [FIPS 202, Appendix B.1].

This file is Mathlib-free.
-/

@[expose] public section

namespace HashSpecs

/-- The `w`-bit big-endian representation of `n`: the most significant bit comes first.
Only the `w` low-order bits of `n` are kept. -/
def natToBitsBE (w n : Nat) : List Bool :=
  (List.range w).reverse.map fun i => n.testBit i

/-- The natural number denoted by a big-endian bit string. -/
def bitsToNatBE (bs : List Bool) : Nat :=
  bs.foldl (fun acc b => 2 * acc + b.toNat) 0

/-- The `w`-bit little-endian representation of `n`: the least significant bit comes first. -/
def natToBitsLE (w n : Nat) : List Bool :=
  (List.range w).map fun i => n.testBit i

/-- The natural number denoted by a little-endian bit string. -/
def bitsToNatLE (bs : List Bool) : Nat :=
  bs.foldr (fun b acc => b.toNat + 2 * acc) 0

/-- The eight bits of a byte, most significant first [FIPS 180-4, §3.1]. -/
def byteToBitsMSB (b : UInt8) : List Bool :=
  natToBitsBE 8 b.toNat

/-- A byte string as a bit string, each byte most significant bit first. -/
def bytesToBitsMSB (bs : List UInt8) : List Bool :=
  bs.flatMap byteToBitsMSB

/-- The eight bits of a byte, least significant first: `h2b` of [FIPS 202, Appendix B.1]. -/
def byteToBitsLSB (b : UInt8) : List Bool :=
  natToBitsLE 8 b.toNat

/-- A byte string as a bit string, each byte least significant bit first. -/
def bytesToBitsLSB (bs : List UInt8) : List Bool :=
  bs.flatMap byteToBitsLSB

/-- Split a list into consecutive pieces of length `n`; the last piece may be shorter.
Defined by structural recursion on a fuel argument so that it reduces in the kernel. -/
def chunks {α : Type} (n : Nat) (l : List α) : List (List α) :=
  go l.length l
where
  /-- `chunks` with an explicit fuel argument. -/
  go : Nat → List α → List (List α)
    | 0, _ => []
    | _ + 1, [] => []
    | k + 1, l@(_ :: _) => l.take n :: go k (l.drop n)

end HashSpecs
