/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Poseidon.Reference

/-!
# Poseidon: fast specification

An executable Poseidon permutation over any commutative ring, with the round constants in an array
and the matrix as a vector of rows, so that nothing is recomputed between rounds. It follows the
reference (`Hash.ZK.Poseidon.Reference`) round by round, and `Hash.ZK.Poseidon.Fast.permutation_eq`
proves that it computes it.

Instantiated at CompPoly's Montgomery representations (Layer 2, `HashZK`), it is the fast
Poseidon over BN254 and the other fields.
-/

@[expose] public section

namespace Hash.ZK.Poseidon.Fast

/-- The parameters of the fast permutation: the round constants in one array, constant
`r · t + i` for element `i` of round `r`, and the matrix as its rows. -/
structure Params (F : Type*) (t : ℕ) where
  /-- The S-box exponent. -/
  α : ℕ
  /-- The number of full rounds. -/
  RF : ℕ
  /-- The number of partial rounds. -/
  RP : ℕ
  /-- The round constants, round by round. -/
  C : Array F
  /-- The rows of the matrix. -/
  M : Vector (Vector F t) t

variable {F : Type*} [CommRing F] {t : ℕ}

/-- The reference parameters the fast ones represent. -/
def Params.toRef (P : Params F t) : Poseidon.Params F t :=
  ⟨P.α, P.RF, P.RP, fun r i => P.C.getD (r * t + i.val) 0, fun i j => P.M[i][j]⟩

/-- The dot product of two vectors. -/
def dot (a b : Vector F t) : F := (List.finRange t).foldl (fun acc j => acc + a[j] * b[j]) 0

variable (P : Params F t)

/-- Round `r`: add the constants, apply the S-box to every element (full round) or the first
(partial round), and multiply by the matrix. -/
def round (s : Vector F t) (r : ℕ) : Vector F t :=
  let full := r < P.RF / 2 || P.RF / 2 + P.RP ≤ r
  let s := Vector.ofFn fun i =>
    let x := s[i] + P.C.getD (r * t + i.val) 0
    if full || i.val = 0 then x ^ P.α else x
  Vector.ofFn fun i => dot P.M[i] s

/-- The Poseidon permutation. -/
def permutation (s : Vector F t) : Vector F t :=
  (List.range (P.RF + P.RP)).foldl (round P) s

/-! ### Equivalence with the reference -/

theorem foldl_add {ι : Type*} (l : List ι) (f : ι → F) (a : F) :
    l.foldl (fun acc j => acc + f j) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

theorem dot_eq (a b : Vector F t) : dot a b = ∑ j : Fin t, a[j] * b[j] := by
  rw [dot, foldl_add _ (fun j => a[j] * b[j]), zero_add, Fin.sum_univ_def]

theorem round_eq (s : Vector F t) (r : ℕ) : round P s r = Reference.round P.toRef s r := by
  ext i hi
  simp only [round, Reference.round, Vector.getElem_ofFn, dot_eq, Matrix.mulVec, dotProduct,
    Reference.sboxLayer, Reference.isFull, Params.toRef, sbox, Fin.getElem_fin]
  rfl

/-- The fast permutation computes the reference. -/
theorem permutation_eq (s : Vector F t) :
    permutation P s = Reference.permutation P.toRef s := by
  unfold permutation Reference.permutation
  change _ = List.foldl _ _ (List.range (P.RF + P.RP))
  congr 1
  funext s r
  exact round_eq P s r

end Hash.ZK.Poseidon.Fast
