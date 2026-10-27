/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import HashZK.Poseidon2
public import HashZK.Raw.Equiv
public import HashZK.Raw.ModPEquiv
public import HashZK.Raw.Poseidon2
public import Hash.Construction.FieldSpongeLemmas
public import Hash.ZK.Poseidon2.Sponge

/-!
# Poseidon2 on raw representations computes the specifications

Each function of `HashZK.Raw.Poseidon2`, on natural numbers, is its instance's specification over
`ZMod p` on the inputs reduced modulo `p`.
-/

@[expose] public section

namespace HashZK.Raw.Poseidon2

open Hash.ZK Hash.ZK.Poseidon2

instance : Fact (Nat.Prime babyBear) := ⟨BabyBear.is_prime⟩

instance : Fact (Nat.Prime koalaBear) := ⟨KoalaBear.is_prime⟩

theorem onModP_eq (I : Plonky3) [Fact I.p.Prime] (hp : 2 < I.p) (h4 : I.t % 4 = 0)
    (xs : Vector ℕ I.t) :
    onModP (I.fastParams (ModP I.p)) xs = (I.permutation (xs.map Nat.cast)).map ZMod.val := by
  have h := I.map_permutation_fastParams h4 (ModP.hom_toZMod hp) (xs.map FieldOps.ofNat)
  have hin : (xs.map FieldOps.ofNat).map ModP.toZMod = xs.map (Nat.cast : ℕ → ZMod I.p) := by
    ext i hi
    simp [ModP.toZMod, FieldOps.ofNat]
  rw [hin] at h
  rw [onModP, ← h, Vector.map_map]
  congr 1
  funext x
  simp [ModP.toZMod, ZMod.val_natCast]

/-- BabyBear width 16 on natural numbers computes its specification. -/
theorem babyBear16_eq (xs : Vector ℕ 16) :
    babyBear16 xs =
      (Plonky3.permutation Hash.ZK.Poseidon2.babyBear16 (xs.map Nat.cast)).map ZMod.val :=
  haveI : Fact (Nat.Prime Hash.ZK.Poseidon2.babyBear16.p) := ⟨BabyBear.is_prime⟩
  onModP_eq Hash.ZK.Poseidon2.babyBear16 (by decide) rfl xs

/-- BabyBear width 24 on natural numbers computes its specification. -/
theorem babyBear24_eq (xs : Vector ℕ 24) :
    babyBear24 xs =
      (Plonky3.permutation Hash.ZK.Poseidon2.babyBear24 (xs.map Nat.cast)).map ZMod.val :=
  haveI : Fact (Nat.Prime Hash.ZK.Poseidon2.babyBear24.p) := ⟨BabyBear.is_prime⟩
  onModP_eq Hash.ZK.Poseidon2.babyBear24 (by decide) rfl xs

/-- KoalaBear width 16 on natural numbers computes its specification. -/
theorem koalaBear16_eq (xs : Vector ℕ 16) :
    koalaBear16 xs =
      (Plonky3.permutation Hash.ZK.Poseidon2.koalaBear16 (xs.map Nat.cast)).map ZMod.val :=
  haveI : Fact (Nat.Prime Hash.ZK.Poseidon2.koalaBear16.p) := ⟨KoalaBear.is_prime⟩
  onModP_eq Hash.ZK.Poseidon2.koalaBear16 (by decide) rfl xs

/-- KoalaBear width 24 on natural numbers computes its specification. -/
theorem koalaBear24_eq (xs : Vector ℕ 24) :
    koalaBear24 xs =
      (Plonky3.permutation Hash.ZK.Poseidon2.koalaBear24 (xs.map Nat.cast)).map ZMod.val :=
  haveI : Fact (Nat.Prime Hash.ZK.Poseidon2.koalaBear24.p) := ⟨KoalaBear.is_prime⟩
  onModP_eq Hash.ZK.Poseidon2.koalaBear24 (by decide) rfl xs

/-- HorizenLabs' BN254 width 3 on natural numbers computes its specification. -/
theorem hlBn254_eq (xs : Vector ℕ 3) :
    hlBn254 xs = (hlBn254Permutation (xs.map Nat.cast)).map ZMod.val := by
  let w : Vector HashZK.Poseidon.Circom.Fr 3 := xs.map Nat.cast
  have hw : xs.map BN254.ofNat = w.map BN254.toRaw := by
    rw [Vector.map_map]
    congr 1
  have hraw := Fast.map_permutation (hlBn254FastParams HashZK.Poseidon.Circom.Fr)
    BN254.hom_toRaw w
  rw [map_hlBn254FastParams BN254.hom_toRaw] at hraw
  have hspec := map_permutation_hlBn254FastParams HashZK.Poseidon2.hom_fr w
  have hin : w.map HashZK.Poseidon.Circom.toZMod = xs.map Nat.cast := by
    rw [Vector.map_map]
    congr 1
    funext n
    exact map_natCast HashZK.Poseidon.Circom.toZMod n
  rw [hin] at hspec
  have hget : paramsBn254.get = hlBn254FastParams BN254.Fr := by
    unfold paramsBn254
    exact HashZK.Raw.Poseidon.thunk_get_mk _
  rw [hlBn254, hw, hget, ← hraw,
    Vector.map_map, ← hspec, Vector.map_map]
  have hcomp : (BN254.toNat ∘ BN254.toRaw) = (ZMod.val ∘ ⇑HashZK.Poseidon.Circom.toZMod) := by
    funext x
    rw [Function.comp_apply, Function.comp_apply]
    exact BN254.toNat_toRaw x
  rw [hcomp]

/-- A raw permutation that computes a Plonky3 instance's specification, cast to `ZMod p`. -/
theorem map_cast_perm (I : Plonky3) [NeZero I.p] (perm : Vector ℕ I.t → Vector ℕ I.t)
    (h : ∀ xs, perm xs = (I.permutation (xs.map Nat.cast)).map ZMod.val) (xs : Vector ℕ I.t) :
    (perm xs).map (Nat.cast : ℕ → ZMod I.p) = I.permutation (xs.map Nat.cast) := by
  rw [h, Vector.map_map]
  ext i hi
  simp

/-- The sponge over a raw permutation computes the sponge over the specification. -/
theorem map_cast_sponge (I : Plonky3) [NeZero I.p] (perm : Vector ℕ I.t → Vector ℕ I.t)
    (h : ∀ xs, perm xs = (I.permutation (xs.map Nat.cast)).map ZMod.val) (rate out : ℕ)
    (hr : 0 < rate) (xs : List ℕ) :
    (sponge perm rate out xs).map (Nat.cast : ℕ → ZMod I.p) =
      I.sponge rate out (xs.map Nat.cast) :=
  Hash.FieldSponge.map_paddingFree _ Nat.cast_zero _ _
    (Hash.FieldSponge.map_onList _ Nat.cast_zero _ _ (map_cast_perm I perm h)) _ _ _ hr xs

/-- The compression over a raw permutation computes the compression over the specification. -/
theorem map_cast_compress (I : Plonky3) [NeZero I.p] (perm : Vector ℕ I.t → Vector ℕ I.t)
    (h : ∀ xs, perm xs = (I.permutation (xs.map Nat.cast)).map ZMod.val) (chunk : ℕ)
    (inputs : List (List ℕ)) :
    (compress perm chunk inputs).map (Nat.cast : ℕ → ZMod I.p) =
      I.compress chunk (inputs.map (·.map Nat.cast)) :=
  Hash.FieldSponge.map_truncatedPermutation _ Nat.cast_zero _ _
    (Hash.FieldSponge.map_onList _ Nat.cast_zero _ _ (map_cast_perm I perm h)) _ _ inputs

/-- BabyBear width 16: Plonky3's sponge on natural numbers computes its specification. -/
theorem babyBear16_sponge_eq (rate out : ℕ) (hr : 0 < rate) (xs : List ℕ) :
    (sponge babyBear16 rate out xs).map (Nat.cast : ℕ → ZMod babyBear) =
      Hash.ZK.Poseidon2.babyBear16.sponge rate out (xs.map Nat.cast) :=
  haveI : NeZero Hash.ZK.Poseidon2.babyBear16.p := ⟨by decide⟩
  map_cast_sponge Hash.ZK.Poseidon2.babyBear16 _ babyBear16_eq rate out hr xs

/-- BabyBear width 16: Plonky3's compression on natural numbers computes its specification. -/
theorem babyBear16_compress_eq (chunk : ℕ) (inputs : List (List ℕ)) :
    (compress babyBear16 chunk inputs).map (Nat.cast : ℕ → ZMod babyBear) =
      Hash.ZK.Poseidon2.babyBear16.compress chunk (inputs.map (·.map Nat.cast)) :=
  haveI : NeZero Hash.ZK.Poseidon2.babyBear16.p := ⟨by decide⟩
  map_cast_compress Hash.ZK.Poseidon2.babyBear16 _ babyBear16_eq chunk inputs

/-- BabyBear width 24: Plonky3's sponge on natural numbers computes its specification. -/
theorem babyBear24_sponge_eq (rate out : ℕ) (hr : 0 < rate) (xs : List ℕ) :
    (sponge babyBear24 rate out xs).map (Nat.cast : ℕ → ZMod babyBear) =
      Hash.ZK.Poseidon2.babyBear24.sponge rate out (xs.map Nat.cast) :=
  haveI : NeZero Hash.ZK.Poseidon2.babyBear24.p := ⟨by decide⟩
  map_cast_sponge Hash.ZK.Poseidon2.babyBear24 _ babyBear24_eq rate out hr xs

/-- BabyBear width 24: Plonky3's compression on natural numbers computes its specification. -/
theorem babyBear24_compress_eq (chunk : ℕ) (inputs : List (List ℕ)) :
    (compress babyBear24 chunk inputs).map (Nat.cast : ℕ → ZMod babyBear) =
      Hash.ZK.Poseidon2.babyBear24.compress chunk (inputs.map (·.map Nat.cast)) :=
  haveI : NeZero Hash.ZK.Poseidon2.babyBear24.p := ⟨by decide⟩
  map_cast_compress Hash.ZK.Poseidon2.babyBear24 _ babyBear24_eq chunk inputs

/-- KoalaBear width 16: Plonky3's sponge on natural numbers computes its specification. -/
theorem koalaBear16_sponge_eq (rate out : ℕ) (hr : 0 < rate) (xs : List ℕ) :
    (sponge koalaBear16 rate out xs).map (Nat.cast : ℕ → ZMod koalaBear) =
      Hash.ZK.Poseidon2.koalaBear16.sponge rate out (xs.map Nat.cast) :=
  haveI : NeZero Hash.ZK.Poseidon2.koalaBear16.p := ⟨by decide⟩
  map_cast_sponge Hash.ZK.Poseidon2.koalaBear16 _ koalaBear16_eq rate out hr xs

/-- KoalaBear width 16: Plonky3's compression on natural numbers computes its specification. -/
theorem koalaBear16_compress_eq (chunk : ℕ) (inputs : List (List ℕ)) :
    (compress koalaBear16 chunk inputs).map (Nat.cast : ℕ → ZMod koalaBear) =
      Hash.ZK.Poseidon2.koalaBear16.compress chunk (inputs.map (·.map Nat.cast)) :=
  haveI : NeZero Hash.ZK.Poseidon2.koalaBear16.p := ⟨by decide⟩
  map_cast_compress Hash.ZK.Poseidon2.koalaBear16 _ koalaBear16_eq chunk inputs

/-- KoalaBear width 24: Plonky3's sponge on natural numbers computes its specification. -/
theorem koalaBear24_sponge_eq (rate out : ℕ) (hr : 0 < rate) (xs : List ℕ) :
    (sponge koalaBear24 rate out xs).map (Nat.cast : ℕ → ZMod koalaBear) =
      Hash.ZK.Poseidon2.koalaBear24.sponge rate out (xs.map Nat.cast) :=
  haveI : NeZero Hash.ZK.Poseidon2.koalaBear24.p := ⟨by decide⟩
  map_cast_sponge Hash.ZK.Poseidon2.koalaBear24 _ koalaBear24_eq rate out hr xs

/-- KoalaBear width 24: Plonky3's compression on natural numbers computes its specification. -/
theorem koalaBear24_compress_eq (chunk : ℕ) (inputs : List (List ℕ)) :
    (compress koalaBear24 chunk inputs).map (Nat.cast : ℕ → ZMod koalaBear) =
      Hash.ZK.Poseidon2.koalaBear24.compress chunk (inputs.map (·.map Nat.cast)) :=
  haveI : NeZero Hash.ZK.Poseidon2.koalaBear24.p := ⟨by decide⟩
  map_cast_compress Hash.ZK.Poseidon2.koalaBear24 _ koalaBear24_eq chunk inputs

end HashZK.Raw.Poseidon2
