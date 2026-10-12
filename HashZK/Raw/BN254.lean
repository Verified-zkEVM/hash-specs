/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Montgomery.Native64x8Defs
public import Hash.ZK.Common.FieldOps
public import Hash.ZK.Common.Primes

/-!
# The BN254 scalar field on raw Montgomery limbs

The operations of CompPoly's eight-limb Montgomery representation of the BN254 scalar field
(`BN254.Fast.ScalarField`), on the bare limbs, without the proof that they are reduced. CompPoly's
runtime definitions (`CompPoly.Fields.Montgomery.Native64x8Defs`) import nothing, so neither does
this module transitively import Mathlib, and the C exports of `HashFFI` can use it.

The constants are those of CompPoly's BN254 instance. `HashZK.Raw.BN254.hom_val` proves that the
limbs of `BN254.Fast.ScalarField` elements map to this representation preserving the operations;
the inverse is `x ^ (p − 2)`, by square-and-multiply.
-/

@[expose] public section

namespace HashZK.Raw.BN254

open Hash.ZK Montgomery.Native64x8

/-- The modulus, in limbs. -/
def q : Limbs8 :=
  ⟨0xf0000001, 0x43e1f593, 0x79b97091, 0x2833e848, 0x8181585d, 0xb85045b6, 0xe131a029,
    0x30644e72⟩

/-- `2²⁵⁶ mod p`, the Montgomery form of one. -/
def r : Limbs8 :=
  ⟨0x4ffffffb, 0xac96341c, 0x9f60cd29, 0x36fc7695, 0x7879462e, 0x666ea36f, 0x9a07df2f,
    0xe0a77c1⟩

/-- `2⁵¹² mod p`, which converts to Montgomery form. -/
def r2 : Limbs8 :=
  ⟨0xae216da7, 0x1bb8e645, 0xe35c59e3, 0x53fe3ab1, 0x53bb8085, 0x8c49833d, 0x7f4e44a5,
    0x216d0b1⟩

/-- `−p⁻¹ mod 2³²`. -/
def negInv : UInt64 := 0xefffffff

/-- A BN254 scalar in Montgomery form, as raw limbs. -/
structure Fr where
  /-- The limbs of the Montgomery residue. -/
  val : Limbs8

/-- The operations without the inverse, from which the inverse is computed. -/
@[instance_reducible] def baseOps : FieldOps Fr where
  zero := ⟨Limbs8.zero⟩
  one := ⟨r⟩
  add x y := ⟨Montgomery.Native64x8.add q x.val y.val⟩
  mul x y := ⟨Montgomery.Native64x8.mul q negInv x.val y.val⟩
  ofNat n := ⟨Montgomery.Native64x8.mul q negInv (Limbs8.ofNat (n % bn254)) r2⟩
  inv x := x

instance : FieldOps Fr :=
  { baseOps with inv := fun x => @FieldOps.pow Fr baseOps x (bn254 - 2) }

/-- The canonical value of an element: one Montgomery reduction, to the natural number. -/
def toNat (x : Fr) : Nat := (Montgomery.Native64x8.mul q negInv x.val Limbs8.one).toNat

/-- The element of a natural number, reduced modulo `p`. -/
def ofNat (n : Nat) : Fr := FieldOps.ofNat n

end HashZK.Raw.BN254
