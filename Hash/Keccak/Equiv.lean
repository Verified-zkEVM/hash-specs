/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Keccak.API
public import Hash.Keccak.Properties

/-!
# Keccak: the fast specification equals the reference

The lane-based Keccak-f[1600] of `Hash.Keccak.Fast` computes the reference Keccak-p[1600, 24] of
`Hash.Keccak.KeccakP` (`Hash.Keccak.Equiv.keccakP_toString`), and the byte-level sponge computes
the reference KECCAK[c] on byte-aligned messages. Consequently each function of
`Hash.Keccak.API` equals its reference, for example `Hash.Keccak.sha3x256_eq`.

The correspondence between the two state representations is `toState`: bit `z` of lane
`x + 5y` is the state bit `A[x, y, z]`.
-/

public section

namespace Hash.Keccak.Equiv

open Fast

/-- The state array denoted by 25 lanes: `A[x, y, z]` is bit `z` of lane `x + 5y`. -/
def toState (a : Array UInt64) : State 64 :=
  fun x y z => (lane a (x.val + 5 * y.val)).toBitVec.getLsbD z.val

theorem lane_tabulate (n : Nat) (f : Nat → UInt64) (i : Nat) (h : i < n) :
    lane (tabulate n f) i = f i := by
  simp [lane, tabulate, h]

theorem val_three : ((3 : Fin 5) : Nat) = 3 := rfl
theorem val_four : ((4 : Fin 5) : Nat) = 4 := rfl

/-! ### The step mappings -/

theorem toState_theta (a : Array UInt64) : toState (theta a) = θ (toState a) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have hxm1 : (x - 1).val = (x.val + 4) % 5 := by rw [Fin.sub_def]; simp; omega
  have hxp1 : (x + 1).val = (x.val + 1) % 5 := by simp [Fin.val_add]
  have hzs : (zsub z 1).val = (z.val + 63) % 64 := by simp [zsub]
  simp only [toState, theta, θ, D, C, lane_tabulate _ _ _ (show x.val + 5 * y.val < 25 by omega),
    show (x.val + 5 * y.val) % 5 = x.val by omega, lane_tabulate _ _ _ hx,
    lane_tabulate _ _ _ (show (x.val + 4) % 5 < 5 by omega),
    lane_tabulate _ _ _ (show (x.val + 1) % 5 < 5 by omega),
    UInt64.toBitVec_xor, BitVec.getLsbD_xor, hxm1, hxp1, hzs,
    show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, UInt64.toBitVec_rotl _ 1 (by decide),
    BitVec.getLsbD_rotateLeft, Fin.val_zero, Fin.val_one, Fin.val_two, val_three, val_four,
    Nat.one_mod, Fin.isValue]
  rcases Nat.eq_zero_or_pos z.val with h0 | h0
  · simp [h0]
  · have : (z.val + 63) % 64 = z.val - 1 := by omega
    simp [this, show ¬ z.val < 1 by omega, hz]

/-- The ρ rotation table agrees with the ρ offsets of the reference. -/
theorem rhoRotations_getD (x y : Fin 5) :
    rhoRotations.getD (x.val + 5 * y.val) 0 = (ρOffset x y % 64).toUInt64 := by
  revert x y
  decide +kernel

theorem toState_rho (a : Array UInt64) : toState (rho a) = ρ (toState a) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have hn : ρOffset x y % 64 < 64 := Nat.mod_lt _ (by decide)
  simp only [toState, rho, ρ, lane_tabulate _ _ _ (show x.val + 5 * y.val < 25 by omega),
    rhoRotations_getD, UInt64.toBitVec_rotl _ _ hn, BitVec.getLsbD_rotateLeft, zsub]
  generalize ρOffset x y = n at hn ⊢
  rw [Nat.mod_mod]
  by_cases h : z.val < n % 64
  · simp [h, show (z.val + (64 - n % 64)) % 64 = 64 - n % 64 + z.val by omega]
  · simp [h, hz, show (z.val + (64 - n % 64)) % 64 = z.val - n % 64 by omega]

theorem toState_pi (a : Array UInt64) : toState (pi a) = π (toState a) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hxy : (x + 3 * y).val = (x.val + 3 * y.val) % 5 := by
    simp only [Fin.val_add, Fin.val_mul]
    rw [show ((3 : Fin 5) : Nat) = 3 from rfl]
    omega
  simp only [toState, pi, π, lane_tabulate _ _ _ (show x.val + 5 * y.val < 25 by omega),
    show (x.val + 5 * y.val) % 5 = x.val by omega, show (x.val + 5 * y.val) / 5 = y.val by omega,
    hxy]

theorem toState_chi (a : Array UInt64) : toState (chi a) = χ (toState a) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have hxp1 : (x + 1).val = (x.val + 1) % 5 := by simp [Fin.val_add]
  have hxp2 : (x + 2).val = (x.val + 2) % 5 := by simp [Fin.val_add]
  simp only [toState, chi, χ, lane_tabulate _ _ _ (show x.val + 5 * y.val < 25 by omega),
    show (x.val + 5 * y.val) % 5 = x.val by omega, show (x.val + 5 * y.val) / 5 = y.val by omega,
    hxp1, hxp2, UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hz, decide_true,
    Bool.true_and, Bool.xor_true]

/-- The round-constant words agree with the round constants of the reference. -/
theorem roundConstantWords_getLsbD (ir : Fin 24) (z : Fin 64) :
    (roundConstantWords.getD ir.val 0).toBitVec.getLsbD z.val = RC 6 ir.val z.val := by
  revert ir z
  decide +kernel

theorem toState_iota (a : Array UInt64) (ir : Nat) (hir : ir < 24) :
    toState (iota a ir) = ι 6 (toState a) ir := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  simp only [toState, iota, ι, lane_tabulate _ _ _ (show x.val + 5 * y.val < 25 by omega)]
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, and_self, ↓reduceIte,
      UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    rw [roundConstantWords_getLsbD ⟨ir, hir⟩ z]
  · have : x.val + 5 * y.val ≠ 0 := by
      intro h0
      exact h ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
    simp [h]

theorem toState_round (a : Array UInt64) (ir : Nat) (hir : ir < 24) :
    toState (round a ir) = Rnd 6 (toState a) ir := by
  rw [round, toState_iota _ _ hir, toState_chi, toState_pi, toState_rho, toState_theta]
  rfl

theorem toState_keccakF (a : Array UInt64) :
    toState (Fast.keccakF a) =
      (List.range 24).foldl (fun A (i : Nat) => Rnd 6 A ((12 + 2 * 6 : Nat) - 24 + i : Int))
        (toState a) := by
  unfold Fast.keccakF
  rw [foldl_hom_of_mem toState round _ (List.range 24) a]
  intro b i hi
  rw [toState_round _ _ (List.mem_range.1 hi)]
  congr 1
  omega

/-- Keccak-f[1600] on lanes computes Keccak-p[1600, 24] on strings. -/
theorem keccakP_toString (a : Array UInt64) :
    keccakP 6 24 (toState a).toString = (toState (Fast.keccakF a)).toString := by
  rw [keccakP_eq_algorithm7 _ _ _ (by simp), State.ofString_toString, toState_keccakF]
  rfl

end Hash.Keccak.Equiv
