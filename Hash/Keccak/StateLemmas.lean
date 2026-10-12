/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Init
public import Hash.Keccak.KeccakP
public import Mathlib.Tactic.Ring

/-!
# Strings and state arrays

The conversions between strings and state arrays of FIPS 202 §3.1.2–3.1.3 are mutually inverse,
and the evaluation-friendly definition `Hash.Keccak.keccakP` is Algorithm 7 as written.
-/

public section

namespace Hash.Keccak

/-- Indexing a concatenation of blocks of a common length `m`. -/
theorem getElem?_flatMap_of_length {α β : Type} (l : List α) (f : α → List β) (m : Nat)
    (hf : ∀ a ∈ l, (f a).length = m) (i j : Nat) (hi : i < l.length) (hj : j < m) :
    (l.flatMap f)[i * m + j]? = (f l[i])[j]? := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.flatMap_cons]
    have ha : (f a).length = m := hf a (by simp)
    cases i with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getElem?_append_left (by omega)]
      rfl
    | succ i =>
      rw [List.getElem?_append_right (by rw [ha, Nat.succ_mul]; omega), ha,
        show (i + 1) * m + j - m = i * m + j by rw [Nat.succ_mul]; omega,
        ih (fun b hb => hf b (by simp [hb])) i (by simpa using hi)]
      rfl

theorem length_flatMap_of_length {α β : Type} (l : List α) (f : α → List β) (m : Nat)
    (hf : ∀ a ∈ l, (f a).length = m) : (l.flatMap f).length = l.length * m := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, hf a (by simp),
      ih (fun b hb => hf b (by simp [hb]))]
    simp [Nat.succ_mul, Nat.add_comm]

namespace State

variable {w : Nat}

@[simp] theorem length_toString (A : State w) : A.toString.length = 25 * w := by
  have hrow : ∀ y : Fin 5, ((List.finRange 5).flatMap fun x =>
      (List.finRange w).map fun z => A x y z).length = 5 * w := by
    intro y
    rw [length_flatMap_of_length _ _ w (by simp)]
    simp
  unfold toString
  rw [length_flatMap_of_length _ _ (5 * w) (fun y _ => hrow y)]
  simp only [List.length_finRange]
  omega

theorem getElem?_toString (A : State w) (x y : Fin 5) (z : Fin w) :
    A.toString[w * (5 * y.val + x.val) + z.val]? = some (A x y z) := by
  have hrow : ∀ y : Fin 5, ((List.finRange 5).flatMap fun x =>
      (List.finRange w).map fun z => A x y z).length = 5 * w := by
    intro y
    rw [length_flatMap_of_length _ _ w (by simp)]
    simp
  have hx : x.val * w + z.val < 5 * w := by
    have := z.isLt
    have := Nat.mul_le_mul_right w (Nat.le_of_lt_succ x.isLt)
    omega
  unfold toString
  rw [show w * (5 * y.val + x.val) + z.val = y.val * (5 * w) + (x.val * w + z.val) by ring,
    getElem?_flatMap_of_length _ _ (5 * w) (fun y _ => hrow y) _ _ (by simp) hx,
    getElem?_flatMap_of_length _ _ w (by simp) _ _ (by simp) z.isLt]
  simp

/-- Every position of a string of length `25w` is `w(5y + x) + z` for some position
`(x, y, z)` of the state. -/
theorem exists_coords {i : Nat} (h : i < 25 * w) :
    ∃ (x y : Fin 5) (z : Fin w), i = w * (5 * y.val + x.val) + z.val := by
  have hw : 0 < w := by omega
  refine ⟨⟨i / w % 5, Nat.mod_lt _ (by decide)⟩, ⟨i / w / 5, ?_⟩, ⟨i % w, Nat.mod_lt _ hw⟩, ?_⟩
  · rw [Nat.div_div_eq_div_mul]
    exact (Nat.div_lt_iff_lt_mul (by omega)).2 (by rw [Nat.mul_comm w 5]; omega)
  · simp only
    have h1 := Nat.div_add_mod i w
    have h2 := Nat.div_add_mod (i / w) 5
    rw [h2]
    exact h1.symm

@[simp] theorem ofString_toString (A : State w) : ofString w A.toString = A := by
  funext x y z
  rw [ofString, List.getD_eq_getElem?_getD, getElem?_toString]
  rfl

@[simp] theorem ofArray_toString (A : State w) : ofArray w A.toString.toArray = A := by
  funext x y z
  rw [ofArray, Array.getD_eq_getD_getElem?, List.getElem?_toArray, getElem?_toString]
  rfl

theorem ofArray_toArray (S : List Bool) : ofArray w S.toArray = ofString w S := by
  funext x y z
  rw [ofArray, ofString, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

theorem toString_ofString (S : List Bool) (h : S.length = 25 * w) :
    (ofString w S).toString = S := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 25 * w
  · obtain ⟨x, y, z, rfl⟩ := exists_coords hi
    rw [getElem?_toString, ofString, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

end State

/-- `Hash.Keccak.keccakP` is Algorithm 7 of FIPS 202 as written: convert the string to a state,
apply the rounds to the state, and convert back. -/
theorem keccakP_eq_algorithm7 (ℓ nr : Nat) (S : List Bool) (hS : S.length = 25 * 2 ^ ℓ) :
    keccakP ℓ nr S =
      ((List.range nr).foldl (fun A (i : Nat) => Rnd ℓ A ((12 + 2 * ℓ : Nat) - nr + i : Int))
        (State.ofString (2 ^ ℓ) S)).toString := by
  unfold keccakP
  simp only []
  -- Every intermediate array holds a string of length `b`.
  have hlen : ∀ (l : List Nat) (a : Array Bool), a.size = 25 * 2 ^ ℓ →
      (l.foldl (fun a (i : Nat) => (State.toString (Rnd ℓ (State.ofArray (2 ^ ℓ) a)
        ((12 + 2 * ℓ : Nat) - nr + i : Int))).toArray) a).size = 25 * 2 ^ ℓ := by
    intro l
    induction l with
    | nil => intro a ha; exact ha
    | cons i l ih => intro a _; exact ih _ (by simp)
  have hfold := List.foldl_hom (State.ofArray (2 ^ ℓ))
    (g₁ := fun a (i : Nat) => (State.toString (Rnd ℓ (State.ofArray (2 ^ ℓ) a)
      ((12 + 2 * ℓ : Nat) - nr + i : Int))).toArray)
    (g₂ := fun A (i : Nat) => Rnd ℓ A ((12 + 2 * ℓ : Nat) - nr + i : Int))
    (l := List.range nr) (init := S.toArray) (fun a i => by simp)
  rw [State.ofArray_toArray] at hfold
  rw [hfold]
  set a := (List.range nr).foldl _ S.toArray
  have ha : a.size = 25 * 2 ^ ℓ := hlen _ _ (by simpa using hS)
  have h : State.ofArray (2 ^ ℓ) a = State.ofString (2 ^ ℓ) a.toList := by
    rw [← State.ofArray_toArray, Array.toArray_toList]
  rw [h, State.toString_ofString _ (by simpa using ha)]

/-- With at least one round, Keccak-p outputs a string of length `b`. -/
theorem length_keccakP (ℓ nr : Nat) (h : 0 < nr) (S : List Bool) :
    (keccakP ℓ nr S).length = 25 * 2 ^ ℓ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h
  unfold keccakP
  simp only [Nat.zero_add, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    State.length_toString]

end Hash.Keccak
