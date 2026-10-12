/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Common.RingOps
public import Hash.ZK.Poseidon.Fast
public import Hash.ZK.Poseidon.Reference

/-!
# Poseidon: the fast permutation computes the reference

In a commutative ring with inverses, the fast permutation (`Hash.ZK.Poseidon.Fast`) computes the
reference permutation (`Hash.ZK.Poseidon.Reference`) with the parameters it represents:
`Hash.ZK.Poseidon.Fast.permutation_eq`.
-/

@[expose] public section

namespace Hash.ZK.Poseidon.Fast

variable {F : Type} [CommRing F] [Inv F] {t : ℕ}

/-- The reference parameters the fast ones represent. -/
def Params.toRef (P : Params F t) : Poseidon.Params F t :=
  ⟨P.α, P.RF, P.RP, fun r i => P.C.getD (r * t + i.val) 0, fun i j => P.M[i][j]⟩

omit [Inv F] in
theorem foldl_add {ι : Type*} (l : List ι) (f : ι → F) (a : F) :
    l.foldl (fun acc j => acc + f j) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

theorem dot_eq (a b : Vector F t) : dot a b = ∑ j : Fin t, a[j] * b[j] := by
  rw [dot, FieldOps.zero_eq]
  simp only [FieldOps.add_eq, FieldOps.mul_eq]
  rw [foldl_add _ (fun j => a[j] * b[j]), zero_add, Fin.sum_univ_def]

variable (P : Params F t)

theorem round_eq (s : Vector F t) (r : ℕ) : round P s r = Reference.round P.toRef s r := by
  ext i hi
  simp only [round, Reference.round, Vector.getElem_ofFn, dot_eq, Matrix.mulVec, dotProduct,
    Reference.sboxLayer, Reference.isFull, Params.toRef, sbox, Fin.getElem_fin, FieldOps.add_eq,
    FieldOps.pow_eq, FieldOps.zero_eq]
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
