/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Common.FieldOps

/-!
# Poseidon2: fast specification

An executable Poseidon2 permutation over the operations of `Hash.ZK.FieldOps`, with the linear
layers computed as the implementations compute them, in `O(t)` operations instead of a
matrix-vector product [Poseidon2, §5, App. B]:

* the external layer of widths 2 and 3 adds the sum of the state to every element;
* the external layer of a width `t = 4k` multiplies each block of four by `M₄`, then adds to
  every element the sum of the elements at the same position in all blocks;
* the internal layer computes `y_i = v_i · x_i + Σ_j x_j`.

`Hash.ZK.Poseidon2.Fast.permutation_eq` proves that it computes the reference in every
commutative ring, and `Hash.ZK.Poseidon2.Fast.map_permutation` that maps preserving the
operations commute with it. The module does not import Mathlib, so that the C exports of
`HashFFI` can use it.

## References

* [Poseidon2] L. Grassi, D. Khovratovich, M. Schofnegger, *Poseidon2: A Faster Version of the
  Poseidon Hash Function*, AFRICACRYPT 2023; ePrint 2023/323. <https://eprint.iacr.org/2023/323>
-/

@[expose] public section

namespace Hash.ZK.Poseidon2.Fast

open FieldOps

/-- The external linear layer. -/
inductive External (F : Type) where
  /-- `circ(2, 1)` or `circ(2, 1, 1)`: add the sum of the state to every element. -/
  | small
  /-- `circ(2·M₄, M₄, …, M₄)`, for a width that is a multiple of 4, with the rows of `M₄`. -/
  | m4 (M4 : Vector (Vector F 4) 4)

/-- The parameters of the fast permutation. -/
structure Params (F : Type) (t : Nat) where
  /-- The S-box exponent `d`. -/
  α : Nat
  /-- The number of external rounds. -/
  RF : Nat
  /-- The number of internal rounds. -/
  RP : Nat
  /-- The external round constants: constant `r · t + i` for element `i` of external round
  `r`. -/
  CE : Array F
  /-- The internal round constants, one per internal round. -/
  CI : Array F
  /-- The external linear layer. -/
  ext : External F
  /-- The internal matrix's diagonal minus one, `v_i = μ_i − 1`. -/
  V : Vector F t

variable {F : Type} [FieldOps F] {t : Nat}

/-- The sum of the elements of a vector. -/
def sum (x : Vector F t) : F :=
  (List.finRange t).foldl (fun acc j => add acc x[j]) zero

/-- Element `k` of a vector, or zero past its end. -/
def get (x : Vector F t) (k : Nat) : F := x.toArray.getD k zero

/-- The external layer of widths 2 and 3. -/
def externalSmall (x : Vector F t) : Vector F t :=
  let s := sum x
  Vector.ofFn fun i => add x[i] s

/-- Each block of four multiplied by `M₄`. -/
def blockMul (M4 : Vector (Vector F 4) 4) (x : Vector F t) : Vector F t :=
  Vector.ofFn fun i =>
    (List.finRange 4).foldl
      (fun acc c => add acc (mul (M4[i.val % 4]'(Nat.mod_lt _ (by decide)))[c]
        (get x (4 * (i.val / 4) + c.val)))) zero

/-- The external layer `circ(2·M₄, M₄, …, M₄)`: the blocks multiplied by `M₄`, plus the sums of
the elements at each position over all blocks. -/
def externalM4 (M4 : Vector (Vector F 4) 4) (x : Vector F t) : Vector F t :=
  let z := blockMul M4 x
  let s : Vector F 4 := Vector.ofFn fun r =>
    (List.range (t / 4)).foldl (fun acc b => add acc (get z (4 * b + r.val))) zero
  Vector.ofFn fun i => add z[i] (s[i.val % 4]'(Nat.mod_lt _ (by decide)))

variable (P : Params F t)

/-- The external linear layer. -/
def external (x : Vector F t) : Vector F t :=
  match P.ext with
  | .small => externalSmall x
  | .m4 M4 => externalM4 M4 x

/-- The internal linear layer, `y_i = v_i · x_i + Σ_j x_j`. -/
def internal (x : Vector F t) : Vector F t :=
  let s := sum x
  Vector.ofFn fun i => add (mul P.V[i] x[i]) s

/-- External round `r`. -/
def externalRound (s : Vector F t) (r : Nat) : Vector F t :=
  external P (Vector.ofFn fun i => pow (add s[i] (P.CE.getD (r * t + i.val) zero)) P.α)

/-- Internal round `r`. -/
def internalRound (s : Vector F t) (r : Nat) : Vector F t :=
  internal P (Vector.ofFn fun i =>
    if i.val = 0 then pow (add s[i] (P.CI.getD r zero)) P.α else s[i])

/-- The Poseidon2 permutation. -/
def permutation (s : Vector F t) : Vector F t :=
  let s := external P s
  let s := (List.range (P.RF / 2)).foldl (externalRound P) s
  let s := (List.range P.RP).foldl (internalRound P) s
  (List.range (P.RF / 2)).foldl (fun s r => externalRound P s (P.RF / 2 + r)) s

/-! ### Maps between representations -/

/-- The external layer mapped by `f`. -/
def External.map {G : Type} (f : F → G) : External F → External G
  | .small => .small
  | .m4 M4 => .m4 (M4.map (·.map f))

/-- The parameters with constants and matrices mapped by `f`. -/
def Params.map {G : Type} (f : F → G) : Params G t :=
  ⟨P.α, P.RF, P.RP, P.CE.map f, P.CI.map f, P.ext.map f, P.V.map f⟩

variable {G : Type} [FieldOps G] {f : F → G}

theorem map_foldl_add {ι : Type} (hf : Hom f) (g : ι → F) (l : List ι) (acc : F) :
    f (l.foldl (fun acc j => add acc (g j)) acc) =
      l.foldl (fun acc j => add acc (f (g j))) (f acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons j l ih => rw [List.foldl_cons, List.foldl_cons, ih, hf.map_add]

theorem map_sum (hf : Hom f) (x : Vector F t) : f (sum x) = sum (x.map f) := by
  rw [sum, map_foldl_add hf (fun j => x[j]), hf.map_zero]
  simp only [sum, Fin.getElem_fin, Vector.getElem_map]

theorem map_getD (hf : Hom f) (C : Array F) (k : Nat) :
    f (C.getD k zero) = (C.map f).getD k zero := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases C[k]? <;> simp [hf.map_zero]

theorem map_get (hf : Hom f) (x : Vector F t) (k : Nat) : f (get x k) = get (x.map f) k := by
  rw [get, get, map_getD hf, Vector.toArray_map]

theorem map_externalSmall (hf : Hom f) (x : Vector F t) :
    (externalSmall x).map f = externalSmall (x.map f) := by
  ext i hi
  simp only [externalSmall, Vector.getElem_map, Vector.getElem_ofFn, hf.map_add, map_sum hf,
    Fin.getElem_fin]

theorem map_blockMul (hf : Hom f) (M4 : Vector (Vector F 4) 4) (x : Vector F t) :
    (blockMul M4 x).map f = blockMul (M4.map (·.map f)) (x.map f) := by
  ext i hi
  simp only [blockMul, Vector.getElem_map, Vector.getElem_ofFn]
  rw [map_foldl_add hf, hf.map_zero]
  simp only [hf.map_mul, map_get hf, Fin.getElem_fin, Vector.getElem_map]

theorem map_externalM4 (hf : Hom f) (M4 : Vector (Vector F 4) 4) (x : Vector F t) :
    (externalM4 M4 x).map f = externalM4 (M4.map (·.map f)) (x.map f) := by
  ext i hi
  simp only [externalM4, Vector.getElem_map, Vector.getElem_ofFn, hf.map_add]
  rw [map_foldl_add hf, hf.map_zero]
  simp only [map_get hf, ← map_blockMul hf, Fin.getElem_fin, Vector.getElem_map]

theorem map_external (hf : Hom f) (x : Vector F t) :
    (external P x).map f = external (P.map f) (x.map f) := by
  unfold external Params.map
  cases P.ext with
  | small => exact map_externalSmall hf x
  | m4 M4 => exact map_externalM4 hf M4 x

theorem map_internal (hf : Hom f) (x : Vector F t) :
    (internal P x).map f = internal (P.map f) (x.map f) := by
  ext i hi
  simp only [internal, Params.map, Vector.getElem_map, Vector.getElem_ofFn, hf.map_add,
    hf.map_mul, map_sum hf, Fin.getElem_fin]

theorem map_externalRound (hf : Hom f) (s : Vector F t) (r : Nat) :
    (externalRound P s r).map f = externalRound (P.map f) (s.map f) r := by
  rw [externalRound, map_external P hf]
  congr 1
  ext i hi
  simp only [Params.map, Vector.getElem_map, Vector.getElem_ofFn, hf.map_pow, hf.map_add,
    map_getD hf, Fin.getElem_fin]

theorem map_internalRound (hf : Hom f) (s : Vector F t) (r : Nat) :
    (internalRound P s r).map f = internalRound (P.map f) (s.map f) r := by
  rw [internalRound, map_internal P hf]
  congr 1
  ext i hi
  simp only [Params.map, Vector.getElem_map, Vector.getElem_ofFn]
  rw [apply_ite f]
  congr 1 <;>
    simp only [hf.map_pow, hf.map_add, map_getD hf, Fin.getElem_fin, Vector.getElem_map]

omit [FieldOps F] [FieldOps G] in
theorem map_foldl {α : Type} (g : Vector F t → α → Vector F t) (g' : Vector G t → α → Vector G t)
    (h : ∀ s a, (g s a).map f = g' (s.map f) a) (l : List α) (s : Vector F t) :
    (l.foldl g s).map f = l.foldl g' (s.map f) := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, List.foldl_cons, ih, h]

/-- A map preserving the operations commutes with the permutation. -/
theorem map_permutation (hf : Hom f) (s : Vector F t) :
    (permutation P s).map f = permutation (P.map f) (s.map f) := by
  simp only [permutation]
  rw [map_foldl (fun s r => externalRound P s (P.RF / 2 + r))
      (fun s r => externalRound (P.map f) s (P.RF / 2 + r))
      (fun s r => map_externalRound P hf s _),
    map_foldl _ _ (map_internalRound P hf), map_foldl _ _ (map_externalRound P hf),
    map_external P hf]
  rfl

end Hash.ZK.Poseidon2.Fast
