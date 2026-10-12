/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Poseidon2.InstanceParams
public import HashZK.Raw.BN254
public import HashZK.Raw.ModP

/-!
# Poseidon2 on raw field representations

The Poseidon2 instances of `Hash.ZK.Poseidon2.InstanceParams` for the C exports of `HashFFI`:
BabyBear and KoalaBear on `HashZK.Raw.ModP`, and BN254 on CompPoly's raw Montgomery limbs. The
functions take and return states of natural numbers; the inputs are reduced modulo `p`, and the
outputs are below `p`. The parameters of each instance are derived once, on first use. The module
does not import Mathlib; `HashZK.Raw.Poseidon2Equiv` proves that each function computes its
specification.
-/

@[expose] public section

namespace HashZK.Raw.Poseidon2

open Hash.ZK Hash.ZK.Poseidon2

/-- The parameters of BabyBear width 16, computed on first use. -/
def paramsBB16 : Thunk (Fast.Params (ModP babyBear) 16) :=
  ⟨fun _ => babyBear16.fastParams (ModP babyBear)⟩

/-- The parameters of BabyBear width 24, computed on first use. -/
def paramsBB24 : Thunk (Fast.Params (ModP babyBear) 24) :=
  ⟨fun _ => babyBear24.fastParams (ModP babyBear)⟩

/-- The parameters of KoalaBear width 16, computed on first use. -/
def paramsKB16 : Thunk (Fast.Params (ModP koalaBear) 16) :=
  ⟨fun _ => koalaBear16.fastParams (ModP koalaBear)⟩

/-- The parameters of KoalaBear width 24, computed on first use. -/
def paramsKB24 : Thunk (Fast.Params (ModP koalaBear) 24) :=
  ⟨fun _ => koalaBear24.fastParams (ModP koalaBear)⟩

/-- The parameters of HorizenLabs' BN254 width 3, computed on first use. -/
def paramsBn254 : Thunk (Fast.Params BN254.Fr 3) := ⟨fun _ => hlBn254FastParams BN254.Fr⟩

/-- A permutation over `ModP p`, on natural numbers. -/
def onModP {p t : Nat} (P : Fast.Params (ModP p) t) (xs : Vector Nat t) : Vector Nat t :=
  (Fast.permutation P (xs.map FieldOps.ofNat)).map fun x => x.val % p

/-- Plonky3's BabyBear Poseidon2 of width 16. -/
def babyBear16 (xs : Vector Nat 16) : Vector Nat 16 := onModP paramsBB16.get xs

/-- Plonky3's BabyBear Poseidon2 of width 24. -/
def babyBear24 (xs : Vector Nat 24) : Vector Nat 24 := onModP paramsBB24.get xs

/-- Plonky3's KoalaBear Poseidon2 of width 16. -/
def koalaBear16 (xs : Vector Nat 16) : Vector Nat 16 := onModP paramsKB16.get xs

/-- Plonky3's KoalaBear Poseidon2 of width 24. -/
def koalaBear24 (xs : Vector Nat 24) : Vector Nat 24 := onModP paramsKB24.get xs

/-- HorizenLabs' BN254 Poseidon2 of width 3. -/
def hlBn254 (xs : Vector Nat 3) : Vector Nat 3 :=
  (Fast.permutation paramsBn254.get (xs.map BN254.ofNat)).map BN254.toNat

end HashZK.Raw.Poseidon2
