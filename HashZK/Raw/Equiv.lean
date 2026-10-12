/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import HashZK.Poseidon.Circom
public import HashZK.Raw.Poseidon

/-!
# The raw limbs compute the specification

The limbs of CompPoly's `BN254.Fast.ScalarField` elements map to the raw representation of
`HashZK.Raw.BN254` preserving the operations (`HashZK.Raw.BN254.hom_toRaw`), so the raw Poseidon
of the C exports computes circomlib's Poseidon (`HashZK.Raw.Poseidon.poseidonNat_eq`).
-/

@[expose] public section

namespace HashZK.Raw.BN254

open Hash.ZK HashZK.Poseidon.Circom

/-- The limbs of an element of CompPoly's `BN254.Fast.ScalarField`. -/
def toRaw (x : HashZK.Poseidon.Circom.Fr) : Fr := ⟨x.val⟩

theorem inv_eq_pow (x : HashZK.Poseidon.Circom.Fr) : x⁻¹ = x ^ (bn254 - 2) := by
  apply toZMod.injective
  rw [map_inv₀, map_pow]
  by_cases h : toZMod x = 0
  · rw [h, inv_zero, zero_pow (by decide)]
  · refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', show bn254 - 2 + 1 = bn254 - 1 from rfl, ZMod.pow_card_sub_one_eq_one h]

/-- The limbs preserve the operations. -/
theorem hom_toRaw : FieldOps.Hom toRaw where
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_neg _ := rfl
  map_mul _ _ := rfl
  map_ofNat _ := rfl
  map_inv x := by
    change toRaw x⁻¹ = @FieldOps.pow Fr baseOps (toRaw x) (bn254 - 2)
    rw [inv_eq_pow, ← FieldOps.pow_eq]
    exact @FieldOps.map_pow _ Fr _ baseOps toRaw rfl (fun _ _ => rfl) x _

/-- The canonical value of the limbs is the value in `ZMod bn254`. -/
theorem toNat_toRaw (x : HashZK.Poseidon.Circom.Fr) : toNat (toRaw x) = (toZMod x).val := by
  change Montgomery.Native64x8.FastField.toNat x = (Montgomery.Native64x8.FastField.toField x).val
  rw [Montgomery.Native64x8.FastField.toField,
    ZMod.val_natCast_of_lt (Montgomery.Native64x8.FastField.toNat_lt x)]

/-- The raw element of a natural number is the limbs of its cast. -/
theorem ofNat_eq (n : ℕ) : ofNat n = toRaw (n : HashZK.Poseidon.Circom.Fr) := rfl

end HashZK.Raw.BN254

namespace HashZK.Raw.Poseidon

open Hash.ZK Hash.ZK.Poseidon HashZK.Raw.BN254 HashZK.Poseidon.Circom

theorem paramsCache_get_toRaw (t : ℕ) :
    (paramsCache t).get =
      (Hash.ZK.Poseidon.Circom.fastParams HashZK.Poseidon.Circom.Fr t).map toRaw := by
  rw [paramsCache_get, Hash.ZK.Poseidon.Circom.map_fastParams hom_toRaw]

theorem initState_map {n : ℕ} (w : Vector HashZK.Poseidon.Circom.Fr n) :
    initState (w.map toRaw) = (Vector.ofFn (Fin.cons 0 fun i => w[i])).map toRaw := by
  ext i hi
  simp only [initState, Vector.getElem_ofFn, Vector.getElem_map]
  cases i with
  | zero => rfl
  | succ i =>
    simp only [Nat.succ_ne_zero, ↓reduceDIte]
    exact congrArg toRaw (Fin.cons_succ (α := fun _ => HashZK.Poseidon.Circom.Fr) 0
      (fun i => w[i]) ⟨i, by omega⟩).symm

/-- The raw Poseidon computes circomlib's Poseidon, on inputs reduced modulo `p`. -/
theorem poseidonNat_eq (inputs : Array ℕ) :
    poseidonNat inputs = (Hash.ZK.Poseidon.Circom.poseidon inputs.size
      fun i => (inputs[i] : ZMod bn254)).val := by
  have hw : inputs.toVector.map ofNat =
      (inputs.toVector.map fun (k : ℕ) => (k : HashZK.Poseidon.Circom.Fr)).map toRaw := by
    rw [Vector.map_map]; rfl
  have hp := Hash.ZK.Poseidon.Circom.map_permutation_fastParams
    (FieldOps.Hom.ofRingHom toZMod.toRingHom (map_inv₀ toZMod)) (inputs.size + 1)
    (Vector.ofFn (Fin.cons 0 fun i =>
      (inputs.toVector.map fun (k : ℕ) => (k : HashZK.Poseidon.Circom.Fr))[i]))
  have h0 := congrArg (·[0]) hp
  simp only [Vector.getElem_map, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h0
  rw [poseidonNat, poseidon, hw, initState_map, paramsCache_get_toRaw,
    ← Fast.map_permutation _ hom_toRaw, Vector.getElem_map, toNat_toRaw]
  change (toZMod _).val = _
  rw [h0, Hash.ZK.Poseidon.Circom.poseidon]
  congr 3
  ext i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  cases i with
  | zero => simp
  | succ i =>
    rw [show (⟨i + 1, hi⟩ : Fin (inputs.size + 1)) = Fin.succ ⟨i, by omega⟩ from rfl,
      Fin.cons_succ, Fin.cons_succ]
    simp

end HashZK.Raw.Poseidon
