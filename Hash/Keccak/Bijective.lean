/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Keccak.StateLemmas
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi

/-!
# Keccak-p is a permutation

Every Keccak-p[b, n_r] permutation of FIPS 202 (`b ∈ {25, 50, …, 1600}`) is a bijection: on state
arrays (`Hash.Keccak.keccakPState_bijective`), and on strings of length `b`
(`Hash.Keccak.keccakP_injective`, `Hash.Keccak.keccakP_surjective`).

Each step mapping is injective, and an injective map from a finite set to itself is bijective.
ρ, π and ι are rearrangements or XORs with constants, and χ acts on each 5-bit row by an
injective map, checked exhaustively. The interesting case is θ. Its effect on column parities is
`c ↦ c ⊕ D(c)`, and θ is injective exactly when this map is. Viewed slice by slice, a column
parity `c` in its kernel satisfies `(I + M) c_z = S c_{z−1}`, where `M` and `S` rotate a 5-bit
slice. Every slice then has even weight, `I + M` is invertible on even-weight slices, so
`c_z = T c_{z−1}` for a fixed map `T`, and going once around the `w` slices gives
`c_z = T^w c_z`. For `w = 2^ℓ` with `ℓ ≤ 6`, an exhaustive check shows that `T^w` fixes no
nonzero even-weight slice, so `c = 0`.

## References

* [FIPS 202] NIST, *SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions*,
  FIPS PUB 202, 2015. <https://doi.org/10.6028/NIST.FIPS.202>
-/

public section

namespace Hash.Keccak

namespace Bijective

/-! ### Five-bit slices and rows, as numbers below 32 -/

/-- The 5-bit vector with bits `n.testBit 0, …, n.testBit 4`. -/
def vec (n : Nat) : Fin 5 → Bool := fun x => n.testBit x.val

/-- The number whose bits are `f 0, …, f 4`. -/
def enc (f : Fin 5 → Bool) : Nat :=
  (f 0).toNat + 2 * (f 1).toNat + 4 * (f 2).toNat + 8 * (f 3).toNat + 16 * (f 4).toNat

theorem enc_lt (f : Fin 5 → Bool) : enc f < 32 := by
  unfold enc
  cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> decide

theorem vec_enc (f : Fin 5 → Bool) : vec (enc f) = f := by
  have key : ∀ a b c d e : Bool, ∀ n : Fin 5,
      (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat).testBit n.val =
        [a, b, c, d, e].getD n.val false := by decide
  funext x
  unfold vec enc
  rw [key]
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨n + 5, h⟩ => exact absurd h (by omega)

/-- Equality of 5-bit vectors, as a Boolean. -/
def eqv (f g : Fin 5 → Bool) : Bool := (List.finRange 5).all fun x => f x == g x

theorem eqv_iff (f g : Fin 5 → Bool) : eqv f g = true ↔ f = g := by
  simp only [eqv, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies]
  exact ⟨fun h => funext h, fun h x => h ▸ rfl⟩

/-- `(I + M) u`: XOR each bit with its neighbour at `x − 1`. -/
def IM (u : Fin 5 → Bool) : Fin 5 → Bool := fun x => u x ^^ u (x - 1)

/-- `S v`: rotate a slice by one position. -/
def S (v : Fin 5 → Bool) : Fin 5 → Bool := fun x => v (x + 1)

/-- Whether a 5-bit number has even weight. -/
def evenB (n : Nat) : Bool := !(vec n 0 ^^ vec n 1 ^^ vec n 2 ^^ vec n 3 ^^ vec n 4)

/-- The slice `u` of even weight with `(I + M) u = S v`, found by search. -/
def T (n : Nat) : Nat :=
  ((List.range 32).find? fun m => evenB m && eqv (IM (vec m)) (S (vec n))).getD 0

/-- `(I + M) u = S v` forces `v` to have even weight. -/
theorem even_of_IM : ∀ m < 32, ∀ n < 32, eqv (IM (vec m)) (S (vec n)) = true → evenB n = true := by
  decide +kernel

/-- `I + M` is invertible on even-weight slices, with inverse given by `T`. -/
theorem eq_T : ∀ m < 32, ∀ n < 32,
    evenB m = true → eqv (IM (vec m)) (S (vec n)) = true → m = T n := by
  decide +kernel

theorem T_lt : ∀ n < 32, T n < 32 := by decide +kernel

/-- `T^(2^ℓ)` fixes no nonzero even-weight slice, for `ℓ ≤ 6`. -/
theorem fixed_T : ∀ ℓ < 7, ∀ n < 32, evenB n = true → Nat.repeat T (2 ^ ℓ) n = n → n = 0 := by
  decide +kernel

/-- χ on one row, `f x ⊕ (¬f (x + 1) ∧ f (x + 2))`. -/
def χrow (f : Fin 5 → Bool) : Fin 5 → Bool := fun x => f x ^^ (!f (x + 1) && f (x + 2))

theorem χrow_injective : ∀ m < 32, ∀ n < 32,
    eqv (χrow (vec m)) (χrow (vec n)) = true → m = n := by
  decide +kernel

/-! ### The steps are injective -/

variable {w : Nat}

theorem χ_injective : Function.Injective (χ (w := w)) := by
  intro A B h
  funext x y z
  have hrow : χrow (fun x => A x y z) = χrow (fun x => B x y z) := by
    funext x'
    have := congrFun (congrFun (congrFun h x') y) z
    simpa [χ, χrow] using this
  have := χrow_injective (enc fun x => A x y z) (enc_lt _) (enc fun x => B x y z) (enc_lt _)
    (by rw [vec_enc, vec_enc, eqv_iff]; exact hrow)
  have := congrArg vec this
  rw [vec_enc, vec_enc] at this
  exact congrFun this x

theorem π_injective : Function.Injective (π (w := w)) := by
  intro A B h
  funext x y z
  -- `(x, y) = (x' + 3y', x')` for `x' = y` and `y' = 2(x − y)`.
  have hc : x = y + 3 * (2 * (x - y)) := by revert x y; decide
  have := congrFun (congrFun (congrFun h y) (2 * (x - y))) z
  simp only [π] at this
  rwa [← hc] at this

theorem zsub_zadd (z : Fin w) (t : Nat) :
    zsub (⟨(z.val + t % w) % w, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) z.isLt)⟩ :
      Fin w) t = z := by
  have hw : 0 < w := Nat.lt_of_le_of_lt (Nat.zero_le _) z.isLt
  have ht := Nat.mod_lt t hw
  have hz := z.isLt
  apply Fin.ext
  simp only [zsub]
  rcases Nat.lt_or_ge (z.val + t % w) w with h | h
  · rw [Nat.mod_eq_of_lt h, show z.val + t % w + (w - t % w) = z.val + w by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hz]
  · rw [show (z.val + t % w) % w = z.val + t % w - w by
        rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)],
      show z.val + t % w - w + (w - t % w) = z.val by omega, Nat.mod_eq_of_lt hz]

theorem ρ_injective : Function.Injective (ρ (w := w)) := by
  intro A B h
  funext x y z
  have := congrFun (congrFun (congrFun h x) y) ⟨(z.val + ρOffset x y % w) % w,
    Nat.mod_lt _ (by have := z.isLt; omega)⟩
  simpa only [ρ, zsub_zadd] using this

theorem ι_injective (ℓ : Nat) (ir : Int) : Function.Injective (fun A => ι ℓ A ir) := by
  intro A B h
  funext x y z
  have := congrFun (congrFun (congrFun h x) y) z
  simp only [ι] at this
  split at this
  · simpa using this
  · exact this

/-- If `T^w` fixes no nonzero even-weight slice, the only column-parity array of lane size `w` in
the kernel of `c ↦ c ⊕ D(c)` is zero. -/
theorem parity_kernel_aux (w : Nat) (hw : 0 < w)
    (hfixed : ∀ n < 32, evenB n = true → Nat.repeat T w n = n → n = 0)
    (c : Fin 5 → Fin w → Bool)
    (hc : ∀ x z, (c x z ^^ c (x - 1) z ^^ c (x + 1) (zsub z 1)) = false) :
    ∀ x z, c x z = false := by
  -- The slices, as numbers below 32.
  let n : Fin w → Nat := fun z => enc fun x => c x z
  have hn : ∀ z, n z < 32 := fun z => enc_lt _
  have hvec : ∀ z, vec (n z) = fun x => c x z := fun z => vec_enc _
  -- The successor of a position, and its predecessor.
  let succ : Fin w → Fin w := fun z => ⟨(z.val + 1) % w, Nat.mod_lt _ hw⟩
  have hpred : ∀ z, zsub (succ z) 1 = z := by
    intro z
    have := zsub_zadd z 1
    rcases Nat.lt_or_ge 1 w with h1 | h1
    · simpa [succ, Nat.mod_eq_of_lt h1] using this
    · have : w = 1 := by omega
      apply Fin.ext
      have := z.isLt
      have := (zsub (succ z) 1).isLt
      omega
  -- `(I + M) c_{z+1} = S c_z`.
  have hrel : ∀ z, IM (vec (n (succ z))) = S (vec (n z)) := by
    intro z
    rw [hvec, hvec]
    funext x
    have := hc x (succ z)
    rw [hpred] at this
    simp only [IM, S]
    revert this
    cases c x (succ z) <;> cases c (x - 1) (succ z) <;> cases c (x + 1) z <;> decide
  have heven : ∀ z, evenB (n z) = true := fun z =>
    even_of_IM _ (hn _) _ (hn _) ((eqv_iff _ _).2 (hrel z))
  have hT : ∀ z, n (succ z) = T (n z) := fun z =>
    eq_T _ (hn _) _ (hn _) (heven _) ((eqv_iff _ _).2 (hrel z))
  -- Going `k` positions forward applies `T` `k` times.
  have hiter : ∀ k z, n ⟨(z.val + k) % w, Nat.mod_lt _ hw⟩ = Nat.repeat T k (n z) := by
    intro k
    induction k with
    | zero => intro z; simp [Nat.mod_eq_of_lt z.isLt, Nat.repeat]
    | succ k ih =>
      intro z
      have e : succ ⟨(z.val + k) % w, Nat.mod_lt _ hw⟩ = ⟨(z.val + (k + 1)) % w, Nat.mod_lt _ hw⟩ :=
        Fin.ext (by simp only [succ, Nat.mod_add_mod, Nat.add_assoc])
      rw [Nat.repeat, ← ih, ← hT, e]
  intro x z
  have hfix := hiter w z
  have e2 : (⟨(z.val + w) % w, Nat.mod_lt _ hw⟩ : Fin w) = z :=
    Fin.ext (show (z.val + w) % w = z.val by rw [Nat.add_mod_right, Nat.mod_eq_of_lt z.isLt])
  rw [e2] at hfix
  have h0 := hfixed _ (hn z) (heven z) hfix.symm
  have := congrFun (hvec z) x
  rw [h0] at this
  rw [← this]
  simp [vec]

/-- For `w = 2^ℓ` with `ℓ ≤ 6`, the only column-parity array in the kernel of
`c ↦ c ⊕ D(c)` is zero. -/
theorem parity_kernel (ℓ : Nat) (hℓ : ℓ < 7) (c : Fin 5 → Fin (2 ^ ℓ) → Bool)
    (hc : ∀ x z, (c x z ^^ c (x - 1) z ^^ c (x + 1) (zsub z 1)) = false) :
    ∀ x z, c x z = false :=
  parity_kernel_aux (2 ^ ℓ) (Nat.two_pow_pos ℓ) (fixed_T ℓ hℓ) c hc

theorem θ_injective (ℓ : Nat) (hℓ : ℓ < 7) : Function.Injective (θ (w := 2 ^ ℓ)) := by
  intro A B h
  -- The column parities of θ(A) are `C(A) ⊕ D(A)`.
  have hC : ∀ (A : State (2 ^ ℓ)) x z, C (θ A) x z = (C A x z ^^ D A x z) := by
    intro A x z
    simp only [C, θ]
    cases A x 0 z <;> cases A x 1 z <;> cases A x 2 z <;> cases A x 3 z <;> cases A x 4 z <;>
      cases D A x z <;> decide
  have hker := parity_kernel ℓ hℓ (fun x z => C A x z ^^ C B x z) (by
    intro x z
    have := hC A x z
    rw [h, hC B x z] at this
    simp only [D] at this
    revert this
    cases C A x z <;> cases C B x z <;> cases C A (x - 1) z <;> cases C B (x - 1) z <;>
      cases C A (x + 1) (zsub z 1) <;> cases C B (x + 1) (zsub z 1) <;> decide)
  have hCAB : ∀ x z, C A x z = C B x z := fun x z => by
    have := hker x z
    revert this
    cases C A x z <;> cases C B x z <;> decide
  funext x y z
  have := congrFun (congrFun (congrFun h x) y) z
  simp only [θ, D, hCAB] at this
  revert this
  cases A x y z <;> cases B x y z <;> cases C B (x - 1) z <;> cases C B (x + 1) (zsub z 1) <;>
    decide

theorem Rnd_injective (ℓ : Nat) (hℓ : ℓ < 7) (ir : Int) :
    Function.Injective (fun A => Rnd ℓ A ir) :=
  (ι_injective ℓ ir).comp (χ_injective.comp (π_injective.comp (ρ_injective.comp
    (θ_injective ℓ hℓ))))

end Bijective

/-- The rounds of Keccak-p[b, n_r] on state arrays [FIPS 202, Algorithm 7, step 2]. -/
def keccakPState (ℓ nr : Nat) (A : State (2 ^ ℓ)) : State (2 ^ ℓ) :=
  (List.range nr).foldl (fun A (i : Nat) => Rnd ℓ A ((12 + 2 * ℓ : Nat) - nr + i : Int)) A

/-- Keccak-p[b, n_r] is a bijection on state arrays, for every `b ∈ {25, 50, …, 1600}`. -/
theorem keccakPState_bijective (ℓ nr : Nat) (hℓ : ℓ < 7) :
    Function.Bijective (keccakPState ℓ nr) := by
  rw [← Finite.injective_iff_bijective]
  unfold keccakPState
  generalize List.range nr = l
  induction l using List.reverseRecOn with
  | nil => exact fun _ _ h => h
  | append_singleton l i ih =>
    intro A B h
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    exact ih (Bijective.Rnd_injective ℓ hℓ _ h)

/-- Keccak-p[b, n_r] is injective on strings of length `b`. -/
theorem keccakP_injective (ℓ nr : Nat) (hℓ : ℓ < 7) {S₁ S₂ : List Bool}
    (h₁ : S₁.length = 25 * 2 ^ ℓ) (h₂ : S₂.length = 25 * 2 ^ ℓ)
    (h : keccakP ℓ nr S₁ = keccakP ℓ nr S₂) : S₁ = S₂ := by
  rw [keccakP_eq_algorithm7 _ _ _ h₁, keccakP_eq_algorithm7 _ _ _ h₂] at h
  have := congrArg (State.ofString (2 ^ ℓ)) h
  simp only [State.ofString_toString] at this
  have := (keccakPState_bijective ℓ nr hℓ).1 this
  rw [← State.toString_ofString S₁ h₁, ← State.toString_ofString S₂ h₂, this]

/-- Every string of length `b` is an output of Keccak-p[b, n_r] on a string of length `b`. -/
theorem keccakP_surjective (ℓ nr : Nat) (hℓ : ℓ < 7) {S : List Bool}
    (h : S.length = 25 * 2 ^ ℓ) : ∃ S', S'.length = 25 * 2 ^ ℓ ∧ keccakP ℓ nr S' = S := by
  obtain ⟨A, hA⟩ := (keccakPState_bijective ℓ nr hℓ).2 (State.ofString (2 ^ ℓ) S)
  refine ⟨A.toString, by simp, ?_⟩
  rw [keccakP_eq_algorithm7 _ _ _ (by simp), State.ofString_toString]
  change (keccakPState ℓ nr A).toString = S
  rw [hA, State.toString_ofString S h]

end Hash.Keccak
