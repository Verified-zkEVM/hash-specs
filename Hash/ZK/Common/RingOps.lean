/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Init
public import Hash.ZK.Common.FieldOps
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Tactic.Ring

/-!
# Field operations of a commutative ring

Every commutative ring with an inverse operation (a field, or `ZMod n`) carries the operations of
`Hash.ZK.FieldOps`, so that the executable instances run in it and can be compared with the
specifications. In it, square-and-multiply computes powers (`Hash.ZK.FieldOps.pow_eq`), and ring
homomorphisms that preserve inverses preserve the operations (`Hash.ZK.FieldOps.Hom.ofRingHom`).
-/

@[expose] public section

namespace Hash.ZK.FieldOps

variable {F : Type} [CommRing F] [Inv F]

/-- The operations of a commutative ring with inverses. -/
instance ofCommRing : FieldOps F where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  ofNat n := n
  inv x := x⁻¹

@[simp] theorem zero_eq : (zero : F) = 0 := rfl
@[simp] theorem one_eq : (one : F) = 1 := rfl
@[simp] theorem add_eq (x y : F) : add x y = x + y := rfl
@[simp] theorem mul_eq (x y : F) : mul x y = x * y := rfl
@[simp] theorem ofNat_eq (n : ℕ) : (ofNat n : F) = n := rfl
@[simp] theorem inv_eq (x : F) : inv x = x⁻¹ := rfl

theorem powAux_eq : ∀ (fuel n : ℕ) (b acc : F), n ≤ fuel → powAux fuel n b acc = acc * b ^ n
  | 0, n, b, acc, h => by rw [Nat.le_zero.mp h, pow_zero, mul_one]; rfl
  | fuel + 1, n, b, acc, h => by
    simp only [powAux]
    split
    · subst n; rw [pow_zero, mul_one]
    · rw [powAux_eq fuel (n / 2) _ _ (by omega)]
      conv_rhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, sq]
      by_cases h2 : n % 2 = 1
      · simp only [h2, ↓reduceIte, pow_one, mul_eq]
        ring
      · simp only [show n % 2 = 0 by omega, Nat.zero_ne_one, ↓reduceIte, pow_zero, mul_one, mul_eq]

/-- Square-and-multiply computes powers. -/
@[simp] theorem pow_eq (x : F) (n : ℕ) : pow x n = x ^ n := by
  rw [pow, powAux_eq n n x one (Nat.le_refl n), one_eq, one_mul]

/-- A ring homomorphism that preserves inverses preserves the operations. -/
theorem Hom.ofRingHom {G : Type} [CommRing G] [Inv G] (φ : F →+* G)
    (hinv : ∀ x, φ x⁻¹ = (φ x)⁻¹) : Hom (φ : F → G) where
  map_zero := _root_.map_zero φ
  map_one := _root_.map_one φ
  map_add := _root_.map_add φ
  map_mul := _root_.map_mul φ
  map_ofNat := map_natCast φ
  map_inv := hinv

end Hash.ZK.FieldOps
