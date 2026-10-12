/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Common.RingOps
public import Hash.ZK.Poseidon2.Fast
public import Hash.ZK.Poseidon2.Reference

/-!
# Poseidon2: the fast permutation computes the reference

In a commutative ring with inverses, the linear layers of the fast permutation
(`Hash.ZK.Poseidon2.Fast`) are the multiplications by the matrices of the reference
(`Hash.ZK.Poseidon2.Reference`): `externalSmall_eq`, `externalM4_eq` (for widths that are
multiples of 4) and `internal_eq`. So the fast permutation computes the reference permutation
with the parameters it represents: `Hash.ZK.Poseidon2.Fast.permutation_eq`.
-/

@[expose] public section

namespace Hash.ZK.Poseidon2.Fast

open Finset

variable {F : Type} [CommRing F] [Inv F] {t : ℕ}

/-- The matrix of an external layer. -/
def External.toMatrix : External F → Matrix (Fin t) (Fin t) F
  | .small => Poseidon2.externalSmall t
  | .m4 M4 => blockCirculant fun a b => M4[a][b]

/-- An external layer `circ(2·M₄, M₄, …)` needs a width that is a multiple of 4. -/
def External.Valid (t : ℕ) : External F → Prop
  | .small => True
  | .m4 _ => t % 4 = 0

/-- The reference parameters the fast ones represent. -/
def Params.toRef (P : Params F t) : Poseidon2.Params F t :=
  ⟨P.α, P.RF, P.RP, fun r i => P.CE.getD (r * t + i.val) 0, fun r => P.CI.getD r 0,
    P.ext.toMatrix, onesPlusDiag fun i => P.V[i]⟩

omit [Inv F] in
theorem foldl_add {ι : Type*} (l : List ι) (g : ι → F) (a : F) :
    l.foldl (fun acc j => acc + g j) a = a + (l.map g).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

omit [Inv F] in
theorem foldl_range (k : ℕ) (g : ℕ → F) (a : F) :
    (List.range k).foldl (fun acc j => acc + g j) a = a + ∑ j ∈ range k, g j := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.foldl_append, ih, sum_range_succ]; simp [add_assoc]

theorem sum_eq (x : Vector F t) : sum x = ∑ j : Fin t, x[j] := by
  simp only [sum, FieldOps.add_eq, FieldOps.zero_eq]
  rw [foldl_add _ (fun j : Fin t => x[j]), zero_add, Fin.sum_univ_def]

theorem get_eq (x : Vector F t) {j : ℕ} (hj : j < t) : get x j = x[j] := by
  simp [get, Array.getD_eq_getD_getElem?, hj]

omit [Inv F] in
theorem onesPlusDiag_mulVec (v x : Fin t → F) (i : Fin t) :
    (onesPlusDiag v).mulVec x i = v i * x i + ∑ j, x j := by
  simp only [Matrix.mulVec, dotProduct, onesPlusDiag]
  have h : ∀ j, (if i = j then 1 + v i else 1) * x j = x j + if i = j then v i * x j else 0 := by
    intro j; split_ifs with h
    · subst h; ring
    · ring
  simp only [h, sum_add_distrib, sum_ite_eq, mem_univ, ite_true]
  ring

theorem externalSmall_eq (x : Vector F t) :
    externalSmall x = Vector.ofFn ((Poseidon2.externalSmall t).mulVec fun i => x[i]) := by
  ext i hi
  simp only [externalSmall, Vector.getElem_ofFn, Poseidon2.externalSmall, onesPlusDiag_mulVec,
    sum_eq, FieldOps.add_eq, Fin.getElem_fin, one_mul]

theorem internal_eq (P : Params F t) (x : Vector F t) :
    internal P x = Vector.ofFn ((onesPlusDiag fun i => P.V[i]).mulVec fun i => x[i]) := by
  ext i hi
  simp only [internal, Vector.getElem_ofFn, onesPlusDiag_mulVec, sum_eq, FieldOps.add_eq,
    FieldOps.mul_eq, Fin.getElem_fin]

omit [Inv F] in
theorem sum_range_four_mul (g : ℕ → F) (k : ℕ) :
    ∑ j ∈ range (4 * k), g j = ∑ b ∈ range k, ∑ c ∈ range 4, g (4 * b + c) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 4 * (k + 1) = 4 * k + 4 by ring, sum_range_add, ih,
      sum_range_succ (fun b => ∑ c ∈ range 4, g (4 * b + c)) k]

/-- Entry `(r, c)` of `M₄`, with indices reduced modulo 4. -/
def m4 (M4 : Vector (Vector F 4) 4) (r c : ℕ) : F :=
  (M4[r % 4]'(Nat.mod_lt _ (by decide)))[c % 4]'(Nat.mod_lt _ (by decide))

theorem blockMul_get (M4 : Vector (Vector F 4) 4) (x : Vector F t) {i : ℕ} (hi : i < t) :
    get (blockMul M4 x) i = ∑ c ∈ range 4, m4 M4 i c * get x (4 * (i / 4) + c) := by
  rw [get_eq _ hi, blockMul, Vector.getElem_ofFn]
  simp only [FieldOps.add_eq, FieldOps.mul_eq, FieldOps.zero_eq]
  rw [foldl_add, zero_add, ← Fin.sum_univ_def, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem externalM4_eq (M4 : Vector (Vector F 4) 4) (h : t % 4 = 0) (x : Vector F t) :
    externalM4 M4 x =
      Vector.ofFn ((blockCirculant fun a b => M4[a][b]).mulVec fun i => x[i]) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = 4 * k := ⟨t / 4, by omega⟩
  ext i hi
  have hq : i / 4 < k := by omega
  -- The fast side: the block product at `i`, plus the sums over the blocks.
  have lhs : (externalM4 M4 x)[i] =
      ∑ c ∈ range 4, m4 M4 i c * get x (4 * (i / 4) + c) +
        ∑ b ∈ range k, ∑ c ∈ range 4, m4 M4 i c * get x (4 * b + c) := by
    simp only [externalM4, Vector.getElem_ofFn, FieldOps.add_eq, FieldOps.zero_eq, Fin.getElem_fin]
    rw [foldl_range, zero_add, ← get_eq _ hi, blockMul_get M4 x hi,
      show 4 * k / 4 = k by omega]
    congr 1
    refine sum_congr rfl fun b hb => ?_
    have hb : b < k := mem_range.mp hb
    rw [blockMul_get M4 x (by omega)]
    refine sum_congr rfl fun c _ => ?_
    simp only [m4, show (4 * b + i % 4) % 4 = i % 4 by omega, show (4 * b + i % 4) / 4 = b by omega]
  -- The reference side: the matrix product, split into blocks.
  have rhs : ((blockCirculant fun a b => M4[a][b]).mulVec fun j : Fin (4 * k) => x[j])
        ⟨i, hi⟩ =
      ∑ b ∈ range k, ∑ c ∈ range 4,
        (if i / 4 = b then 2 else 1) * (m4 M4 i c * get x (4 * b + c)) := by
    simp only [Matrix.mulVec, dotProduct, blockCirculant]
    let G : ℕ → F := fun j => (if i / 4 = j / 4 then 2 else 1) * (m4 M4 i j * get x j)
    calc _ = ∑ j : Fin (4 * k), G j.val := by
          refine sum_congr rfl fun j _ => ?_
          simp only [G, m4, Fin.getElem_fin, get_eq x j.isLt]
          ring
      _ = ∑ j ∈ range (4 * k), G j := Fin.sum_univ_eq_sum_range G _
      _ = ∑ b ∈ range k, ∑ c ∈ range 4, G (4 * b + c) := sum_range_four_mul G k
      _ = _ := by
          refine sum_congr rfl fun b _ => sum_congr rfl fun c hc => ?_
          have hc : c < 4 := mem_range.mp hc
          simp only [G, m4, show (4 * b + c) / 4 = b by omega,
            show (4 * b + c) % 4 = c % 4 by omega]
  rw [lhs, Vector.getElem_ofFn, rhs]
  have split : ∀ b c, (if i / 4 = b then (2 : F) else 1) * (m4 M4 i c * get x (4 * b + c)) =
      m4 M4 i c * get x (4 * b + c) + if i / 4 = b then m4 M4 i c * get x (4 * b + c) else 0 := by
    intro b c; split_ifs <;> ring
  simp only [split, sum_add_distrib]
  rw [add_comm]
  congr 1
  rw [sum_comm]
  simp only [sum_ite_eq, mem_range, hq, ite_true]

variable (P : Params F t)

theorem external_eq (hv : P.ext.Valid t) (x : Vector F t) :
    external P x = Vector.ofFn (P.toRef.ME.mulVec fun i => x[i]) := by
  unfold external Params.toRef
  cases hP : P.ext with
  | small => exact externalSmall_eq x
  | m4 M4 =>
    rw [hP] at hv
    exact externalM4_eq M4 hv x

theorem externalRound_eq (hv : P.ext.Valid t) (s : Vector F t) (r : ℕ) :
    externalRound P s r = Reference.externalRound P.toRef s r := by
  rw [externalRound, external_eq P hv, Reference.externalRound]
  congr 2
  funext i
  simp only [Vector.getElem_ofFn, FieldOps.pow_eq, FieldOps.add_eq, FieldOps.zero_eq, sbox,
    Params.toRef, Fin.getElem_fin]

theorem internalRound_eq (s : Vector F t) (r : ℕ) :
    internalRound P s r = Reference.internalRound P.toRef s r := by
  rw [internalRound, internal_eq, Reference.internalRound]
  congr 2
  funext i
  simp only [Vector.getElem_ofFn, FieldOps.pow_eq, FieldOps.add_eq, FieldOps.zero_eq, sbox,
    Params.toRef, Fin.getElem_fin]

/-- The fast permutation computes the reference. -/
theorem permutation_eq (hv : P.ext.Valid t) (s : Vector F t) :
    permutation P s = Reference.permutation P.toRef s := by
  simp only [permutation, Reference.permutation, external_eq P hv]
  have he : externalRound P = Reference.externalRound P.toRef := by
    funext s r; exact externalRound_eq P hv s r
  have hi : internalRound P = Reference.internalRound P.toRef := by
    funext s r; exact internalRound_eq P s r
  rw [he, hi]
  rfl

end Hash.ZK.Poseidon2.Fast
