/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

/-!
# Field operations of the executable instances

The executable versions of the ZK-friendly hashes are written once, over the few operations of
`FieldOps`, and run on several representations of a field: any commutative ring with inverses
(through `Hash.ZK.FieldOps.ofCommRing`, used in the proofs), CompPoly's Montgomery field types
(Layer 2), and their raw limb arithmetic (the C exports of `HashFFI`). A map between
representations that preserves the operations, `FieldOps.Hom`, commutes with every computation
written over them, which is how the results proved for one representation carry to the others.

The module does not import Mathlib, so that the C exports can use it.
-/

@[expose] public section

namespace Hash.ZK

/-- The field operations used by the executable instances. -/
class FieldOps (F : Type) where
  /-- The zero element. -/
  zero : F
  /-- The unit element. -/
  one : F
  /-- Addition. -/
  add : F → F → F
  /-- Multiplication. -/
  mul : F → F → F
  /-- The image of a natural number. -/
  ofNat : Nat → F
  /-- The inverse (of a nonzero element). -/
  inv : F → F

namespace FieldOps

variable {F : Type} [FieldOps F]

/-- Square-and-multiply with fuel: `acc · bⁿ`, reading `n` from its least significant bit. -/
def powAux : Nat → Nat → F → F → F
  | 0, _, _, acc => acc
  | fuel + 1, n, b, acc =>
    if n = 0 then acc
    else powAux fuel (n / 2) (mul b b) (if n % 2 = 1 then mul acc b else acc)

/-- `x ^ n`, by square-and-multiply. -/
def pow (x : F) (n : Nat) : F := powAux n n x one

/-- A map between representations that preserves the operations. -/
structure Hom {A B : Type} [FieldOps A] [FieldOps B] (f : A → B) : Prop where
  map_zero : f zero = zero
  map_one : f one = one
  map_add : ∀ x y, f (add x y) = add (f x) (f y)
  map_mul : ∀ x y, f (mul x y) = mul (f x) (f y)
  map_ofNat : ∀ n, f (ofNat n) = ofNat n
  map_inv : ∀ x, f (inv x) = inv (f x)

/-- Square-and-multiply commutes with a map that preserves the unit and multiplication. -/
theorem map_powAux {A B : Type} [FieldOps A] [FieldOps B] {f : A → B} (hone : f one = one)
    (hmul : ∀ x y, f (mul x y) = mul (f x) (f y)) :
    ∀ (fuel n : Nat) (b acc : A), f (powAux fuel n b acc) = powAux fuel n (f b) (f acc)
  | 0, _, _, _ => rfl
  | fuel + 1, n, b, acc => by
    simp only [powAux]
    split
    · rfl
    · rw [map_powAux hone hmul fuel, hmul]
      congr 1
      split <;> simp only [hmul]

theorem map_pow {A B : Type} [FieldOps A] [FieldOps B] {f : A → B} (hone : f one = one)
    (hmul : ∀ x y, f (mul x y) = mul (f x) (f y)) (x : A) (n : Nat) :
    f (pow x n) = pow (f x) n := by
  rw [pow, pow, map_powAux hone hmul, hone]

theorem Hom.map_pow {A B : Type} [FieldOps A] [FieldOps B] {f : A → B} (hf : Hom f) (x : A)
    (n : Nat) : f (pow x n) = pow (f x) n :=
  FieldOps.map_pow hf.map_one hf.map_mul x n

end FieldOps

end Hash.ZK
