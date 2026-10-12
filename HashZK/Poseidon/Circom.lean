/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Poseidon.Circom
public import CompPoly.Fields.BN254.Fast

/-!
# Fast circomlib Poseidon over CompPoly's BN254

circomlib's Poseidon (`Hash.ZK.Poseidon.Circom`) computed in CompPoly's eight-limb Montgomery
representation of the BN254 scalar field, `BN254.Fast.ScalarField`. The parameters of each width
are derived once, on first use.

`HashZK.Poseidon.Circom.poseidon_eq` proves that, through CompPoly's ring isomorphism with
`ZMod bn254`, it computes the specification: the fast permutation computes the reference
(`Hash.ZK.Poseidon.Fast.permutation_eq`), the fast permutation commutes with maps preserving the
field operations (`Hash.ZK.Poseidon.Fast.map_permutation`), and so do the parameters
(`Hash.ZK.Poseidon.Circom.map_fastParams`).
-/

@[expose] public section

namespace HashZK.Poseidon.Circom

open Hash.ZK Hash.ZK.Poseidon Hash.ZK.Poseidon.Circom

/-- The BN254 scalar field in CompPoly's Montgomery representation. -/
abbrev Fr : Type := BN254.Fast.ScalarField

theorem bn254_eq : bn254 = BN254.scalarFieldSize := rfl

instance : Fact (Nat.Prime bn254) := bn254_eq ▸ inferInstance

/-- CompPoly's ring isomorphism between the Montgomery representation and `ZMod bn254`. -/
def toZMod : Fr ≃+* ZMod bn254 := BN254.Fast.ringEquiv

/-- The parameters of width 2, computed on first use. -/
def params2 : Thunk (Fast.Params Fr 2) := ⟨fun _ => fastParams Fr 2⟩

/-- The parameters of width 3, computed on first use. -/
def params3 : Thunk (Fast.Params Fr 3) := ⟨fun _ => fastParams Fr 3⟩

/-- The parameters of width 4, computed on first use. -/
def params4 : Thunk (Fast.Params Fr 4) := ⟨fun _ => fastParams Fr 4⟩

/-- The parameters of width 5, computed on first use. -/
def params5 : Thunk (Fast.Params Fr 5) := ⟨fun _ => fastParams Fr 5⟩

/-- The parameters of width 6, computed on first use. -/
def params6 : Thunk (Fast.Params Fr 6) := ⟨fun _ => fastParams Fr 6⟩

/-- The parameters of width 7, computed on first use. -/
def params7 : Thunk (Fast.Params Fr 7) := ⟨fun _ => fastParams Fr 7⟩

/-- The parameters of width 8, computed on first use. -/
def params8 : Thunk (Fast.Params Fr 8) := ⟨fun _ => fastParams Fr 8⟩

/-- The parameters of width 9, computed on first use. -/
def params9 : Thunk (Fast.Params Fr 9) := ⟨fun _ => fastParams Fr 9⟩

/-- The parameters of width 10, computed on first use. -/
def params10 : Thunk (Fast.Params Fr 10) := ⟨fun _ => fastParams Fr 10⟩

/-- The parameters of width 11, computed on first use. -/
def params11 : Thunk (Fast.Params Fr 11) := ⟨fun _ => fastParams Fr 11⟩

/-- The parameters of width 12, computed on first use. -/
def params12 : Thunk (Fast.Params Fr 12) := ⟨fun _ => fastParams Fr 12⟩

/-- The parameters of width 13, computed on first use. -/
def params13 : Thunk (Fast.Params Fr 13) := ⟨fun _ => fastParams Fr 13⟩

/-- The parameters of width 14, computed on first use. -/
def params14 : Thunk (Fast.Params Fr 14) := ⟨fun _ => fastParams Fr 14⟩

/-- The parameters of width 15, computed on first use. -/
def params15 : Thunk (Fast.Params Fr 15) := ⟨fun _ => fastParams Fr 15⟩

/-- The parameters of width 16, computed on first use. -/
def params16 : Thunk (Fast.Params Fr 16) := ⟨fun _ => fastParams Fr 16⟩

/-- The parameters of width 17, computed on first use. -/
def params17 : Thunk (Fast.Params Fr 17) := ⟨fun _ => fastParams Fr 17⟩

/-- The parameters of the width-`t` instance in `Fr`, computed once for `t = 2 … 17`. -/
def paramsCache (t : ℕ) : Thunk (Fast.Params Fr t) :=
  if h : t = 2 then h ▸ params2
  else if h : t = 3 then h ▸ params3
  else if h : t = 4 then h ▸ params4
  else if h : t = 5 then h ▸ params5
  else if h : t = 6 then h ▸ params6
  else if h : t = 7 then h ▸ params7
  else if h : t = 8 then h ▸ params8
  else if h : t = 9 then h ▸ params9
  else if h : t = 10 then h ▸ params10
  else if h : t = 11 then h ▸ params11
  else if h : t = 12 then h ▸ params12
  else if h : t = 13 then h ▸ params13
  else if h : t = 14 then h ▸ params14
  else if h : t = 15 then h ▸ params15
  else if h : t = 16 then h ▸ params16
  else if h : t = 17 then h ▸ params17
  else ⟨fun _ => fastParams Fr t⟩

theorem thunk_get_mk {α : Type} (f : Unit → α) : (Thunk.mk f).get = f () := rfl

theorem dite_get {t k : ℕ} (p : Thunk (Fast.Params Fr k)) (hp : p.get = fastParams Fr k)
    (e : Thunk (Fast.Params Fr t)) (he : e.get = fastParams Fr t) :
    (if h : t = k then h ▸ p else e).get = fastParams Fr t := by
  by_cases h : t = k
  · subst h; rw [dite_eq_left rfl]; exact hp
  · rw [dite_eq_right h]; exact he

theorem paramsCache_get (t : ℕ) : (paramsCache t).get = fastParams Fr t := by
  unfold paramsCache
  iterate 16 refine dite_get _ (thunk_get_mk _) _ ?_
  exact thunk_get_mk _

/-- circomlib's `PoseidonEx` in `Fr`: hash the inputs with initial capacity element
`initState`, and output the first `nOut` elements of the state. -/
def poseidonEx (initState : Fr) (inputs : Array Fr) (nOut : ℕ) : List Fr :=
  (Fast.permutation (paramsCache (inputs.size + 1)).get
    (Vector.ofFn (Fin.cons initState fun i => inputs[i]))).toList.take nOut

/-- circomlib's `Poseidon` in `Fr`: the first output element, with initial capacity element 0. -/
def poseidon (inputs : Array Fr) : Fr :=
  (Fast.permutation (paramsCache (inputs.size + 1)).get
    (Vector.ofFn (Fin.cons 0 fun i => inputs[i])))[0]

/-- The fast permutation in `Fr` computes the specification's permutation in `ZMod bn254`. -/
theorem permutation_eq (t : ℕ) (s : Vector Fr t) :
    (Fast.permutation (paramsCache t).get s).map toZMod =
      Reference.permutation (Hash.ZK.Poseidon.Circom.params t) (s.map toZMod) := by
  rw [paramsCache_get]
  exact map_permutation_fastParams (FieldOps.Hom.ofRingHom toZMod.toRingHom (map_inv₀ toZMod)) t s

/-- The fast Poseidon computes circomlib's Poseidon. -/
theorem poseidon_eq (inputs : Array Fr) :
    toZMod (poseidon inputs) =
      Hash.ZK.Poseidon.Circom.poseidon inputs.size fun i => toZMod inputs[i] := by
  have h := congrArg (·[0]) (permutation_eq (inputs.size + 1)
    (Vector.ofFn (Fin.cons 0 fun i => inputs[i])))
  simp only [Vector.getElem_map] at h
  rw [poseidon, h, Hash.ZK.Poseidon.Circom.poseidon]
  congr 2
  ext i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  cases i with
  | zero => simp
  | succ i =>
    rw [show (⟨i + 1, hi⟩ : Fin (inputs.size + 1)) = Fin.succ ⟨i, by omega⟩ from rfl,
      Fin.cons_succ, Fin.cons_succ]

end HashZK.Poseidon.Circom
