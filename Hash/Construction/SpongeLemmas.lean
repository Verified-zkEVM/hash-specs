/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Init
public import Hash.Construction.Sponge

/-!
# Properties of the sponge construction

The main result is *prefix consistency*: asking a sponge for fewer output bits gives a prefix of
the longer output (`Hash.Sponge.sponge_prefix`). This is what makes a sponge an
extendable-output function.
-/

public section

namespace Hash.Sponge

variable (f : List Bool → List Bool) (r : Nat)

theorem squeeze_add (S : List Bool) (k j : Nat) :
    ∃ S', squeeze f r S (k + j) = squeeze f r S k ++ squeeze f r S' j := by
  induction k generalizing S with
  | zero => exact ⟨S, by simp [squeeze]⟩
  | succ k ih =>
    obtain ⟨S', h⟩ := ih (f S)
    exact ⟨S', by rw [Nat.succ_add, squeeze, squeeze, h, List.append_assoc]⟩

theorem length_squeeze (b : Nat) (hrb : r ≤ b) (hf : ∀ S, (f S).length = b) (S : List Bool)
    (hS : S.length = b) (k : Nat) : (squeeze f r S k).length = k * r := by
  induction k generalizing S with
  | zero => simp [squeeze]
  | succ k ih =>
    rw [squeeze, List.length_append, ih _ (hf S), List.length_take, hS, Nat.min_eq_left hrb,
      Nat.succ_mul, Nat.add_comm]

theorem length_absorb (b c : Nat) (hf : ∀ S, (f S).length = b) (S : List Bool)
    (hS : S.length = b) (Ps : List (List Bool)) : (absorb f c S Ps).length = b := by
  induction Ps generalizing S with
  | nil => exact hS
  | cons P Ps ih => exact ih _ (hf _)

/-- `max 1 ⌈d / r⌉` blocks of `r` bits hold at least `d` bits. -/
theorem le_blocks_mul (d : Nat) (hr : 0 < r) : d ≤ max 1 ((d + r - 1) / r) * r := by
  have h := Nat.div_add_mod (d + r - 1) r
  have hm := Nat.mod_lt (d + r - 1) hr
  have : d ≤ (d + r - 1) / r * r := by rw [Nat.mul_comm]; omega
  exact Nat.le_trans this (Nat.mul_le_mul_right _ (by omega))

theorem blocks_mono {d₁ d₂ : Nat} (h : d₁ ≤ d₂) :
    max 1 ((d₁ + r - 1) / r) ≤ max 1 ((d₂ + r - 1) / r) := by
  have := Nat.div_le_div_right (c := r) (show d₁ + r - 1 ≤ d₂ + r - 1 by omega)
  omega

/-- Prefix consistency: for a permutation `f` of `b`-bit strings and `0 < r ≤ b`, the first
`d₁` output bits of the sponge are the same whatever longer output length `d₂` is asked for. -/
theorem sponge_prefix (pad : Nat → Nat → List Bool) (b : Nat) (hr : 0 < r) (hrb : r ≤ b)
    (hf : ∀ S, (f S).length = b) (N : List Bool) {d₁ d₂ : Nat} (h : d₁ ≤ d₂) :
    sponge f pad b r N d₁ = (sponge f pad b r N d₂).take d₁ := by
  unfold sponge
  simp only []
  set S := absorb f (b - r) (List.replicate b false) (chunks r (N ++ pad r N.length))
  have hS : S.length = b := length_absorb f b _ hf _ (by simp) _
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (blocks_mono r h)
  obtain ⟨S', hS'⟩ := squeeze_add f r S (max 1 ((d₁ + r - 1) / r)) j
  rw [hj, hS', List.take_take, Nat.min_eq_left h, List.take_append_of_le_length
    (by rw [length_squeeze f r b hrb hf S hS]; exact le_blocks_mul r d₁ hr)]

end Hash.Sponge
