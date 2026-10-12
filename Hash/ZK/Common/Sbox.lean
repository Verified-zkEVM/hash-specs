/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Init
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Power S-boxes

The nonlinear layer of Poseidon, Poseidon2, Rescue-Prime and MiMC is the power map
`x ↦ x ^ α` on a finite field `𝔽_q` [Poseidon, §2.3; Rescue-Prime, §2.1]. It is a permutation of
`𝔽_q` exactly when `gcd(α, q − 1) = 1`, and its inverse is again a power map, `x ↦ x ^ β` with
`α β ≡ 1 (mod q − 1)`: Rescue-Prime uses it as the inverse S-box `x ↦ x ^ (1/α)`.

## Main results

* `Hash.ZK.sbox_sbox_invExponent`: `x ^ α ^ β = x` for the inverse exponent `β`.
* `Hash.ZK.sbox_bijective`: the power map is a bijection when `gcd(α, q − 1) = 1`.

## References

* [Poseidon] L. Grassi, D. Khovratovich, C. Rechberger, A. Roy, M. Schofnegger, *Poseidon: A New
  Hash Function for Zero-Knowledge Proof Systems*, USENIX Security 2021.
  <https://eprint.iacr.org/2019/458>
* [Rescue-Prime] A. Szepieniec, T. Ashur, S. Dhooghe, *Rescue-Prime: a Standard Specification
  (SoK)*, 2020. <https://eprint.iacr.org/2020/1143>
-/

@[expose] public section

namespace Hash.ZK

/-- The power S-box `x ↦ x ^ α` [Poseidon, §2.3]. -/
def sbox {M : Type*} [Monoid M] (α : ℕ) (x : M) : M := x ^ α

/-- A ring homomorphism commutes with the S-box. -/
theorem map_sbox {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (α : ℕ) (x : R) :
    φ (sbox α x) = sbox α (φ x) := map_pow φ x α

variable {F : Type*} [Field F]

/-- An inverse of the exponent `α` modulo `q − 1`: the `β < q − 1` with `α β ≡ 1 (mod q − 1)`
when `gcd(α, q − 1) = 1` [Rescue-Prime, §2.1]. -/
def invExponent (α q : ℕ) : ℕ := ((α : ZMod (q - 1))⁻¹).val

theorem mul_invExponent_mod (α q : ℕ) (hq : 2 < q) (h : Nat.Coprime α (q - 1)) :
    α * invExponent α q % (q - 1) = 1 := by
  have hn : NeZero (q - 1) := ⟨by omega⟩
  have h1 : ((α * invExponent α q : ℕ) : ZMod (q - 1)) = 1 := by
    rw [Nat.cast_mul, invExponent, ZMod.natCast_zmod_val, ZMod.coe_mul_inv_eq_one α h]
  rw [← ZMod.val_natCast, h1, ZMod.val_one'' (by omega)]

/-- A power `x ^ m` with `m ≡ 1 (mod q − 1)` and `m ≥ 1` is the identity on `𝔽_q`. -/
theorem pow_eq_self_of_mod [Fintype F] (m : ℕ) (hm : 0 < m)
    (h : m % (Fintype.card F - 1) = 1 % (Fintype.card F - 1)) (x : F) : x ^ m = x := by
  by_cases hx : x = 0
  · rw [hx, zero_pow (by omega)]
  · have hd := Nat.div_add_mod (m - 1) (Fintype.card F - 1)
    rw [Nat.sub_mod_eq_zero_of_mod_eq (by rw [h]), Nat.add_zero] at hd
    rw [show m = (Fintype.card F - 1) * ((m - 1) / (Fintype.card F - 1)) + 1 by omega,
      pow_succ, pow_mul, FiniteField.pow_card_sub_one_eq_one x hx, one_pow, one_mul]

/-- The inverse S-box undoes the S-box [Rescue-Prime, §2.1]. -/
theorem sbox_sbox_invExponent [Fintype F] (α : ℕ) (hq : 2 < Fintype.card F)
    (h : Nat.Coprime α (Fintype.card F - 1)) (x : F) :
    sbox (invExponent α (Fintype.card F)) (sbox α x) = x := by
  have hm := mul_invExponent_mod α _ hq h
  unfold sbox
  rw [← pow_mul]
  apply pow_eq_self_of_mod _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at hm)
  rw [hm, Nat.one_mod_eq_one.2 (by omega)]

/-- The S-box undoes the inverse S-box. -/
theorem sbox_invExponent_sbox [Fintype F] (α : ℕ) (hq : 2 < Fintype.card F)
    (h : Nat.Coprime α (Fintype.card F - 1)) (x : F) :
    sbox α (sbox (invExponent α (Fintype.card F)) x) = x := by
  have hm := mul_invExponent_mod α _ hq h
  unfold sbox
  rw [← pow_mul, Nat.mul_comm]
  apply pow_eq_self_of_mod _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at hm)
  rw [hm, Nat.one_mod_eq_one.2 (by omega)]

/-- The power map `x ↦ x ^ α` is a permutation of `𝔽_q` when `gcd(α, q − 1) = 1`
[Poseidon, §2.3]. -/
theorem sbox_bijective [Fintype F] (α : ℕ) (hq : 2 < Fintype.card F)
    (h : Nat.Coprime α (Fintype.card F - 1)) : Function.Bijective (sbox (M := F) α) :=
  ⟨Function.LeftInverse.injective (sbox_sbox_invExponent α hq h),
    Function.RightInverse.surjective (sbox_invExponent_sbox α hq h)⟩

end Hash.ZK
