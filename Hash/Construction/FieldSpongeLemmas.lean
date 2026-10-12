/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Construction.FieldSponge
public import Hash.Prelude.BitsLemmas

/-!
# Properties of the field sponges

* `absorb_append`: absorbing a block-aligned prefix and then the rest is absorbing everything.
* `map_paddingFree`, `map_truncatedPermutation`: a map that commutes with the permutations and
  preserves the default element commutes with the sponge and the compression. This carries the
  correctness of a permutation's implementation to the sponge built on it.
-/

@[expose] public section

namespace Hash.FieldSponge

variable {α β : Type}

theorem chunks_append_mul (n : ℕ) (hn : 0 < n) (k : ℕ) (a b : List α) (ha : a.length = k * n) :
    chunks n (a ++ b) = chunks n a ++ chunks n b := by
  induction k generalizing a with
  | zero =>
    have : a = [] := List.eq_nil_of_length_eq_zero (by simpa using ha)
    subst this
    simp [chunks_nil]
  | succ k ih =>
    rw [Nat.succ_mul] at ha
    have hlen : (a.take n).length = n := by simp; omega
    have hdrop : (a.drop n).length = k * n := by simp; omega
    conv_lhs => rw [← List.take_append_drop n a, List.append_assoc]
    rw [chunks_append n hn _ _ hlen, ih _ hdrop]
    conv_rhs => rw [← List.take_append_drop n a, chunks_append n hn _ _ hlen]
    rfl

/-- Absorbing a prefix whose length is a multiple of the rate, and then the rest, is absorbing
everything: an incremental sponge agrees with the one-shot definition. -/
theorem absorb_append (perm : List α → List α) (rate : ℕ) (hr : 0 < rate) (k : ℕ)
    (state xs ys : List α) (hxs : xs.length = k * rate) :
    absorb perm state (chunks rate (xs ++ ys)) =
      absorb perm (absorb perm state (chunks rate xs)) (chunks rate ys) := by
  rw [chunks_append_mul rate hr k xs ys hxs, absorb, List.foldl_append]
  rfl

theorem map_overwrite (f : α → β) (block state : List α) :
    (overwrite block state).map f = overwrite (block.map f) (state.map f) := by
  simp [overwrite, List.map_drop]

theorem map_absorb (f : α → β) (P : List α → List α) (Q : List β → List β)
    (h : ∀ l, (P l).map f = Q (l.map f)) (state : List α) (blocks : List (List α)) :
    (absorb P state blocks).map f = absorb Q (state.map f) (blocks.map (·.map f)) := by
  induction blocks generalizing state with
  | nil => rfl
  | cons b bs ih =>
    simp only [absorb, List.foldl_cons, List.map_cons] at ih ⊢
    rw [ih, h, map_overwrite]

theorem map_chunks (f : α → β) (n : ℕ) (hn : 0 < n) (l : List α) :
    (chunks n l).map (·.map f) = chunks n (l.map f) := by
  rw [chunks_eq_map_range n hn, chunks_eq_map_range n hn, List.length_map, List.map_map]
  congr 1
  funext i
  simp [List.map_take, List.map_drop]

/-- A map that commutes with the permutations and preserves the default element commutes with
the padding-free sponge. -/
theorem map_paddingFree [Inhabited α] [Inhabited β] (f : α → β) (hf : f default = default)
    (P : List α → List α) (Q : List β → List β) (h : ∀ l, (P l).map f = Q (l.map f))
    (width rate out : ℕ) (hr : 0 < rate) (xs : List α) :
    (paddingFree P width rate out xs).map f = paddingFree Q width rate out (xs.map f) := by
  simp only [paddingFree, List.map_take]
  rw [map_absorb f P Q h, List.map_replicate, hf, map_chunks f rate hr]

/-- A map that commutes with the permutations and preserves the default element commutes with
the truncated permutation. -/
theorem map_truncatedPermutation [Inhabited α] [Inhabited β] (f : α → β)
    (hf : f default = default) (P : List α → List α) (Q : List β → List β)
    (h : ∀ l, (P l).map f = Q (l.map f)) (width chunk : ℕ) (inputs : List (List α)) :
    (truncatedPermutation P width chunk inputs).map f =
      truncatedPermutation Q width chunk (inputs.map (·.map f)) := by
  simp only [truncatedPermutation, List.map_take, h, List.map_append, List.map_replicate, hf,
    List.map_flatten, List.length_flatten, List.map_map]
  congr 4
  simp [Function.comp_def]

/-- A map that commutes with permutations of vectors commutes with them as functions on lists. -/
theorem map_onList [Inhabited α] [Inhabited β] {t : ℕ} (f : α → β) (hf : f default = default)
    (P : Vector α t → Vector α t) (Q : Vector β t → Vector β t)
    (h : ∀ v, (P v).map f = Q (v.map f)) (l : List α) :
    (onList P l).map f = onList Q (l.map f) := by
  rw [onList, onList, ← Vector.toList_map, h]
  congr 2
  ext i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases l[i]? <;> simp [hf]

end Hash.FieldSponge
