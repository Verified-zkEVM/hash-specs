/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Common.RingOps
public import HashZK.Raw.ModP
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Small prime fields on natural numbers compute in `ZMod p`

The map from `HashZK.Raw.ModP p` to `ZMod p` preserves the operations when `p` is a prime above 2
(`HashZK.Raw.ModP.hom_toZMod`).
-/

@[expose] public section

namespace HashZK.Raw.ModP

open Hash.ZK

variable {p : ℕ}

/-- The value of a representative in `ZMod p`. -/
def toZMod (x : ModP p) : ZMod p := x.val

theorem inv_eq_pow [Fact p.Prime] (hp : 2 < p) (x : ZMod p) : x⁻¹ = x ^ (p - 2) := by
  by_cases h : x = 0
  · rw [h, inv_zero, zero_pow (by omega)]
  · refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', show p - 2 + 1 = p - 1 by omega, ZMod.pow_card_sub_one_eq_one h]

/-- The map to `ZMod p` preserves the operations. -/
theorem hom_toZMod [Fact p.Prime] (hp : 2 < p) : FieldOps.Hom (toZMod (p := p)) where
  map_zero := by simp [toZMod, FieldOps.zero]
  map_one := by simp [toZMod, FieldOps.one]
  map_add x y := by simp [toZMod, FieldOps.add]
  map_neg x := by
    change ((((p - x.val % p) % p : ℕ)) : ZMod p) = -(x.val : ZMod p)
    rw [ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt _ (by omega)).le, ZMod.natCast_self,
      ZMod.natCast_mod, zero_sub]
  map_mul x y := by simp [toZMod, FieldOps.mul]
  map_ofNat n := by simp [toZMod, FieldOps.ofNat]
  map_inv x := by
    change toZMod (@FieldOps.pow (ModP p) (baseOps p) x (p - 2)) = (toZMod x)⁻¹
    rw [inv_eq_pow hp, ← FieldOps.pow_eq]
    exact @FieldOps.map_pow _ (ZMod p) (baseOps p) _ toZMod (by simp [toZMod, FieldOps.one])
      (fun a b => by simp [toZMod, FieldOps.mul]) x _

end HashZK.Raw.ModP
