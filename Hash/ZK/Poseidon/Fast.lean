/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Common.FieldOps

/-!
# Poseidon: fast specification

An executable Poseidon permutation over the operations of `Hash.ZK.FieldOps`, with the round
constants in an array and the matrix as a vector of rows, so that nothing is recomputed between
rounds. It follows the reference (`Hash.ZK.Poseidon.Reference`) round by round;
`Hash.ZK.Poseidon.Fast.permutation_eq` proves that it computes it in every commutative ring, and
`Hash.ZK.Poseidon.Fast.map_permutation` that maps preserving the operations commute with it.

The module does not import Mathlib, so that the C exports of `HashFFI` can use it.
-/

@[expose] public section

namespace Hash.ZK.Poseidon.Fast

open FieldOps

/-- The parameters of the fast permutation: the round constants in one array, constant
`r · t + i` for element `i` of round `r`, and the matrix as its rows. -/
structure Params (F : Type) (t : Nat) where
  /-- The S-box exponent. -/
  α : Nat
  /-- The number of full rounds. -/
  RF : Nat
  /-- The number of partial rounds. -/
  RP : Nat
  /-- The round constants, round by round. -/
  C : Array F
  /-- The rows of the matrix. -/
  M : Vector (Vector F t) t

variable {F : Type} [FieldOps F] {t : Nat}

/-- The dot product of two vectors. -/
def dot (a b : Vector F t) : F :=
  (List.finRange t).foldl (fun acc j => add acc (mul a[j] b[j])) zero

variable (P : Params F t)

/-- Round `r`: add the constants, apply the S-box to every element (full round) or the first
(partial round), and multiply by the matrix. -/
def round (s : Vector F t) (r : Nat) : Vector F t :=
  let full := r < P.RF / 2 || P.RF / 2 + P.RP ≤ r
  let s := Vector.ofFn fun i =>
    let x := add s[i] (P.C.getD (r * t + i.val) zero)
    if full || i.val = 0 then pow x P.α else x
  Vector.ofFn fun i => dot P.M[i] s

/-- The Poseidon permutation. -/
def permutation (s : Vector F t) : Vector F t :=
  (List.range (P.RF + P.RP)).foldl (round P) s

/-! ### Maps between representations -/

/-- The parameters with constants and matrix mapped by `f`. -/
def Params.map {G : Type} (f : F → G) : Params G t :=
  ⟨P.α, P.RF, P.RP, P.C.map f, P.M.map (·.map f)⟩

variable {G : Type} [FieldOps G] {f : F → G}

theorem map_foldl_dot (hf : Hom f) (a b : Vector F t) (l : List (Fin t)) (acc : F) :
    f (l.foldl (fun acc j => add acc (mul a[j] b[j])) acc) =
      l.foldl (fun acc j => add acc (mul (a.map f)[j] (b.map f)[j])) (f acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [ih, hf.map_add, hf.map_mul]
    simp only [Fin.getElem_fin, Vector.getElem_map]

theorem map_dot (hf : Hom f) (a b : Vector F t) : f (dot a b) = dot (a.map f) (b.map f) := by
  rw [dot, map_foldl_dot hf, hf.map_zero]
  rfl

theorem map_getD (hf : Hom f) (C : Array F) (k : Nat) :
    f (C.getD k zero) = (C.map f).getD k zero := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases C[k]? <;> simp [hf.map_zero]

theorem map_round (hf : Hom f) (s : Vector F t) (r : Nat) :
    (round P s r).map f = round (P.map f) (s.map f) r := by
  ext i hi
  simp only [round, Params.map, Vector.getElem_map, Vector.getElem_ofFn]
  rw [map_dot hf]
  congr 1
  · simp only [Fin.getElem_fin, Vector.getElem_map]
  · ext j hj
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    rw [apply_ite f]
    congr 1 <;>
      simp only [hf.map_pow, hf.map_add, map_getD hf, Fin.getElem_fin, Vector.getElem_map]

/-- A map preserving the operations commutes with the permutation. -/
theorem map_permutation (hf : Hom f) (s : Vector F t) :
    (permutation P s).map f = permutation (P.map f) (s.map f) := by
  unfold permutation
  change _ = List.foldl _ _ (List.range (P.RF + P.RP))
  generalize List.range (P.RF + P.RP) = rs
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => rw [List.foldl_cons, List.foldl_cons, ih, map_round P hf]

end Hash.ZK.Poseidon.Fast
