/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Poseidon2.Instances
public import CompPoly.Fields.BabyBear.Fast
public import CompPoly.Fields.KoalaBear.Fast
public import HashZK.Poseidon.Circom

/-!
# Fast Poseidon2 over CompPoly's fields

The Poseidon2 instances of `Hash.ZK.Poseidon2.Instances` computed in CompPoly's Montgomery
representations: BabyBear and KoalaBear in one 32-bit word (`BabyBear.Fast.Field`,
`KoalaBear.Fast.Field`), and the BN254 scalar field in eight limbs (`BN254.Fast.ScalarField`). The
parameters of each instance are derived once, on first use.

Through CompPoly's ring isomorphisms with `ZMod p`, each computes its specification: the fast
permutation commutes with maps preserving the field operations and computes the reference
(`Hash.ZK.Poseidon2.Plonky3.map_permutation_fastParams`,
`Hash.ZK.Poseidon2.map_permutation_hlBn254FastParams`).
-/

@[expose] public section

namespace HashZK.Poseidon2

open Hash.ZK Hash.ZK.Poseidon2

/-- BabyBear in CompPoly's Montgomery representation. -/
abbrev BB : Type := BabyBear.Fast.Field

/-- KoalaBear in CompPoly's Montgomery representation. -/
abbrev KB : Type := KoalaBear.Fast.Field

/-- The BN254 scalar field in CompPoly's Montgomery representation. -/
abbrev Fr : Type := HashZK.Poseidon.Circom.Fr

/-- The parameters of BabyBear width 16, computed on first use. -/
def paramsBB16 : Thunk (Fast.Params BB 16) := ⟨fun _ => babyBear16.fastParams BB⟩

/-- The parameters of BabyBear width 24, computed on first use. -/
def paramsBB24 : Thunk (Fast.Params BB 24) := ⟨fun _ => babyBear24.fastParams BB⟩

/-- The parameters of KoalaBear width 16, computed on first use. -/
def paramsKB16 : Thunk (Fast.Params KB 16) := ⟨fun _ => koalaBear16.fastParams KB⟩

/-- The parameters of KoalaBear width 24, computed on first use. -/
def paramsKB24 : Thunk (Fast.Params KB 24) := ⟨fun _ => koalaBear24.fastParams KB⟩

/-- The parameters of HorizenLabs' BN254 width 3, computed on first use. -/
def paramsBn254 : Thunk (Fast.Params Fr 3) := ⟨fun _ => hlBn254FastParams Fr⟩

/-- Plonky3's BabyBear Poseidon2 of width 16. -/
def babyBear16 (s : Vector BB 16) : Vector BB 16 := Fast.permutation paramsBB16.get s

/-- Plonky3's BabyBear Poseidon2 of width 24. -/
def babyBear24 (s : Vector BB 24) : Vector BB 24 := Fast.permutation paramsBB24.get s

/-- Plonky3's KoalaBear Poseidon2 of width 16. -/
def koalaBear16 (s : Vector KB 16) : Vector KB 16 := Fast.permutation paramsKB16.get s

/-- Plonky3's KoalaBear Poseidon2 of width 24. -/
def koalaBear24 (s : Vector KB 24) : Vector KB 24 := Fast.permutation paramsKB24.get s

/-- HorizenLabs' BN254 Poseidon2 of width 3. -/
def hlBn254 (s : Vector Fr 3) : Vector Fr 3 := Fast.permutation paramsBn254.get s

theorem hom_bb : FieldOps.Hom (BabyBear.Fast.ringEquiv : BB → ZMod Hash.ZK.babyBear) :=
  FieldOps.Hom.ofRingHom BabyBear.Fast.ringEquiv.toRingHom (map_inv₀ BabyBear.Fast.ringEquiv)

theorem hom_kb : FieldOps.Hom (KoalaBear.Fast.ringEquiv : KB → ZMod Hash.ZK.koalaBear) :=
  FieldOps.Hom.ofRingHom KoalaBear.Fast.ringEquiv.toRingHom (map_inv₀ KoalaBear.Fast.ringEquiv)

theorem hom_fr : FieldOps.Hom (HashZK.Poseidon.Circom.toZMod : Fr → ZMod bn254) :=
  FieldOps.Hom.ofRingHom HashZK.Poseidon.Circom.toZMod.toRingHom
    (map_inv₀ HashZK.Poseidon.Circom.toZMod)

/-- BabyBear width 16 computes its specification. -/
theorem babyBear16_eq (s : Vector BB 16) :
    (babyBear16 s).map BabyBear.Fast.ringEquiv =
      Plonky3.permutation Hash.ZK.Poseidon2.babyBear16 (s.map BabyBear.Fast.ringEquiv) :=
  Plonky3.map_permutation_fastParams Hash.ZK.Poseidon2.babyBear16 rfl hom_bb s

/-- BabyBear width 24 computes its specification. -/
theorem babyBear24_eq (s : Vector BB 24) :
    (babyBear24 s).map BabyBear.Fast.ringEquiv =
      Plonky3.permutation Hash.ZK.Poseidon2.babyBear24 (s.map BabyBear.Fast.ringEquiv) :=
  Plonky3.map_permutation_fastParams Hash.ZK.Poseidon2.babyBear24 rfl hom_bb s

/-- KoalaBear width 16 computes its specification. -/
theorem koalaBear16_eq (s : Vector KB 16) :
    (koalaBear16 s).map KoalaBear.Fast.ringEquiv =
      Plonky3.permutation Hash.ZK.Poseidon2.koalaBear16 (s.map KoalaBear.Fast.ringEquiv) :=
  Plonky3.map_permutation_fastParams Hash.ZK.Poseidon2.koalaBear16 rfl hom_kb s

/-- KoalaBear width 24 computes its specification. -/
theorem koalaBear24_eq (s : Vector KB 24) :
    (koalaBear24 s).map KoalaBear.Fast.ringEquiv =
      Plonky3.permutation Hash.ZK.Poseidon2.koalaBear24 (s.map KoalaBear.Fast.ringEquiv) :=
  Plonky3.map_permutation_fastParams Hash.ZK.Poseidon2.koalaBear24 rfl hom_kb s

/-- HorizenLabs' BN254 width 3 computes its specification. -/
theorem hlBn254_eq (s : Vector Fr 3) :
    (hlBn254 s).map HashZK.Poseidon.Circom.toZMod =
      hlBn254Permutation (s.map HashZK.Poseidon.Circom.toZMod) :=
  map_permutation_hlBn254FastParams hom_fr s

end HashZK.Poseidon2
