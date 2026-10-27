/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Poseidon.CircomParams
public import HashZK.Raw.BN254

/-!
# circomlib's Poseidon on raw BN254 limbs

circomlib's Poseidon (`Hash.ZK.Poseidon.Circom`) computed on the raw Montgomery limbs of
`HashZK.Raw.BN254`, for the C exports of `HashFFI`. The module does not transitively import
Mathlib. The parameters of each width are derived once, on first use.

`HashZK.Raw.Poseidon.poseidonNat_eq` proves that `poseidonNat` computes the specification.
-/

@[expose] public section

namespace HashZK.Raw.Poseidon

open Hash.ZK Hash.ZK.Poseidon Hash.ZK.Poseidon.Circom HashZK.Raw.BN254

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

/-- The parameters of the width-`t` instance, computed once for `t = 2 … 17`. -/
def paramsCache (t : Nat) : Thunk (Fast.Params Fr t) :=
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

theorem dite_get {t k : Nat} (p : Thunk (Fast.Params Fr k)) (hp : p.get = fastParams Fr k)
    (e : Thunk (Fast.Params Fr t)) (he : e.get = fastParams Fr t) :
    (if h : t = k then h ▸ p else e).get = fastParams Fr t := by
  by_cases h : t = k
  · subst h; rw [dite_eq_left rfl]; exact hp
  · rw [dite_eq_right h]; exact he

theorem paramsCache_get (t : Nat) : (paramsCache t).get = fastParams Fr t := by
  unfold paramsCache
  iterate 16 refine dite_get _ (thunk_get_mk _) _ ?_
  exact thunk_get_mk _

/-- The initial state `[0, x₁, …, x_n]`. -/
def initState {n : Nat} (inputs : Vector Fr n) : Vector Fr (n + 1) :=
  Vector.ofFn fun i => if h : i.val = 0 then FieldOps.zero else inputs[i.val - 1]

/-- circomlib's `Poseidon(n)`: the first element of the permutation of `[0, x₁, …, x_n]`. -/
def poseidon {n : Nat} (inputs : Vector Fr n) : Fr :=
  (Fast.permutation (paramsCache (n + 1)).get (initState inputs))[0]

/-- circomlib's `Poseidon` on canonical values: the inputs are reduced modulo `p`, and the output
is below `p`. -/
def poseidonNat (inputs : Array Nat) : Nat :=
  toNat (poseidon (inputs.toVector.map ofNat))

end HashZK.Raw.Poseidon
