/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Poseidon2.Equiv
public import Hash.ZK.Poseidon2.InstanceParams
public import Mathlib.Data.ZMod.Basic

/-!
# Poseidon2: the instances over `ZMod p`

The Poseidon2 instances of `Hash.ZK.Poseidon2.InstanceParams` as reference parameters over
`ZMod p`: HorizenLabs' BN254 instance of width 3 (`hlBn254Params`), and Plonky3's BabyBear and
KoalaBear instances (`Plonky3.params`). Their constants are drawn from the Grain LFSR; the
matrices are those of the paper and the implementations (see `InstanceParams`).

`Hash.ZK.Poseidon2.Plonky3.map_permutation_fastParams` and
`Hash.ZK.Poseidon2.map_permutation_hlBn254FastParams` prove that the fast permutation, in any
representation of the field related to `ZMod p` by a map preserving the operations, computes these
instances.
-/

@[expose] public section

namespace Hash.ZK.Poseidon2

/-- The value of a dyadic rational `±a / 2^b` in `ZMod p`. -/
def Dyadic.val {p : ℕ} (d : Dyadic) : ZMod p :=
  let x := (d.num : ZMod p) * ((2 ^ d.exp : ℕ) : ZMod p)⁻¹
  if d.neg then -x else x

/-- The reference parameters of a Plonky3 instance over `ZMod p` [Plonky3]: Grain constants, the
external matrix `circ(2·M₄, M₄, …)` with `M₄ = circ(2, 3, 1, 1)`, and the internal matrix with
diagonal `1 + v_i`. -/
def Plonky3.params (I : Plonky3) : Params (ZMod I.p) I.t :=
  let (ce, ci) := I.samples
  { α := I.α
    RF := 8
    RP := I.RP
    CE := fun r i => (ce.getD (r * I.t + i.val) 0 : ZMod I.p)
    CI := fun r => (ci.getD r 0 : ZMod I.p)
    ME := blockCirculant fun a b => (((plonky3M4.getD a.val []).getD b.val 0 : ℕ) : ZMod I.p)
    MI := onesPlusDiag fun i => (I.diag.getD i.val (dy 0)).val }

/-- A Plonky3 instance's permutation over `ZMod p`. -/
def Plonky3.permutation (I : Plonky3) (s : Vector (ZMod I.p) I.t) : Vector (ZMod I.p) I.t :=
  Reference.permutation I.params s

/-- The reference parameters of HorizenLabs' BN254 instance of width 3 with the given samples:
`d = 5`, `R_F = 8`, `R_P = 56`, `M_E = circ(2, 1, 1)` and `M_I = [[2,1,1],[1,2,1],[1,1,3]]`
[HorizenLabs, `poseidon2_instance_bn256.rs`]. -/
def hlBn254ParamsOf (samples : List ℕ × List ℕ) : Params (ZMod bn254) 3 where
  α := 5
  RF := 8
  RP := 56
  CE r i := (samples.1.getD (r * 3 + i.val) 0 : ZMod bn254)
  CI r := (samples.2.getD r 0 : ZMod bn254)
  ME := externalSmall 3
  MI := onesPlusDiag ![1, 1, 2]

/-- The reference parameters of HorizenLabs' BN254 instance of width 3. -/
def hlBn254Params : Params (ZMod bn254) 3 := hlBn254ParamsOf hlBn254Samples

/-- HorizenLabs' BN254 Poseidon2 permutation of width 3. -/
def hlBn254Permutation (s : Vector (ZMod bn254) 3) : Vector (ZMod bn254) 3 :=
  Reference.permutation hlBn254Params s

/-! ### The fast instances compute the specification -/

theorem Dyadic.toF_eq {p : ℕ} (d : Dyadic) : (d.toF : ZMod p) = d.val := by
  unfold Dyadic.toF Dyadic.val
  cases d.neg <;> simp

theorem getD_ofNat {p : ℕ} (l : List ℕ) (k : ℕ) :
    ((l.map fun c => (FieldOps.ofNat c : ZMod p)).toArray.getD k 0) = (l.getD k 0 : ZMod p) := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  cases l[k]?
  · simp only [Option.map_none, Option.getD_none, Nat.cast_zero]
  · simp only [Option.map_some, Option.getD_some, FieldOps.ofNat_eq]

theorem Plonky3.fastParams_toRef (I : Plonky3) :
    (I.fastParams (ZMod I.p)).toRef = I.params := by
  unfold Plonky3.fastParams Plonky3.params
  generalize I.samples = s
  rcases s with ⟨ce, ci⟩
  simp only [Fast.Params.toRef, getD_ofNat]
  simp only [Fast.External.toMatrix, Vector.getElem_ofFn, Fin.getElem_fin, FieldOps.ofNat_eq,
    Dyadic.toF_eq]

theorem hlBn254FastParamsOf_toRef (samples : List ℕ × List ℕ) :
    (hlBn254FastParamsOf (ZMod bn254) samples).toRef = hlBn254ParamsOf samples := by
  simp only [hlBn254FastParamsOf, hlBn254ParamsOf, Fast.Params.toRef, getD_ofNat]
  simp only [Fast.External.toMatrix]
  congr
  funext i
  fin_cases i <;> simp

theorem Plonky3.valid (I : Plonky3) (h4 : I.t % 4 = 0) (F : Type) [FieldOps F] :
    (I.fastParams F).ext.Valid I.t := by
  unfold Plonky3.fastParams
  generalize I.samples = s
  rcases s with ⟨ce, ci⟩
  exact h4

/-- The fast permutation, with a Plonky3 instance's parameters in any representation `F` of the
field, computes the instance through a map `f : F → ZMod p` that preserves the operations. -/
theorem Plonky3.map_permutation_fastParams (I : Plonky3) (h4 : I.t % 4 = 0) {F : Type}
    [FieldOps F] {f : F → ZMod I.p} (hf : FieldOps.Hom f) (s : Vector F I.t) :
    (Fast.permutation (I.fastParams F) s).map f = I.permutation (s.map f) := by
  rw [Fast.map_permutation _ hf, I.map_fastParams hf, Fast.permutation_eq _ (I.valid h4 _),
    I.fastParams_toRef]
  rfl

theorem map_permutation_hlBn254FastParamsOf (samples : List ℕ × List ℕ) {F : Type} [FieldOps F]
    {f : F → ZMod bn254} (hf : FieldOps.Hom f) (s : Vector F 3) :
    (Fast.permutation (hlBn254FastParamsOf F samples) s).map f =
      Reference.permutation (hlBn254ParamsOf samples) (s.map f) := by
  rw [Fast.map_permutation _ hf, map_hlBn254FastParamsOf hf,
    Fast.permutation_eq _ (by simp only [hlBn254FastParamsOf, Fast.External.Valid]),
    hlBn254FastParamsOf_toRef]

/-- The fast permutation, with HorizenLabs' BN254 parameters in any representation `F` of the
field, computes the instance through a map `f : F → ZMod bn254` that preserves the operations. -/
theorem map_permutation_hlBn254FastParams {F : Type} [FieldOps F] {f : F → ZMod bn254}
    (hf : FieldOps.Hom f) (s : Vector F 3) :
    (Fast.permutation (hlBn254FastParams F) s).map f = hlBn254Permutation (s.map f) :=
  map_permutation_hlBn254FastParamsOf _ hf s

end Hash.ZK.Poseidon2
