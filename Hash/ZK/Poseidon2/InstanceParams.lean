/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Common.Grain
public import Hash.ZK.Common.Primes
public import Hash.ZK.Poseidon2.Fast

/-!
# Poseidon2: the parameters of the instances

The data of the Poseidon2 instances in use, and the parameters of the fast permutation built from
them in any representation of the field. `Hash.ZK.Poseidon2.Instances` states the instances over
`ZMod p`.

* *HorizenLabs BN254, width 3* [HorizenLabs, `poseidon2_instance_bn256.rs`]: `d = 5`, `R_F = 8`,
  `R_P = 56`, external matrix `circ(2, 1, 1)`, internal matrix `[[2,1,1],[1,2,1],[1,1,3]]`.
* *Plonky3 BabyBear and KoalaBear, widths 16, 24 and 32* [Plonky3, `baby-bear/src/poseidon2.rs`,
  `koala-bear/src/poseidon2.rs`]: `d = 7` (BabyBear) or `3` (KoalaBear), `R_F = 8`, `R_P` per
  width, external matrix `circ(2·M₄, M₄, …)` with Plonky3's `M₄ = circ(2, 3, 1, 1)` (not the
  paper's), and hand-picked internal diagonals `v_i = ±2^a` or `±1/2^b`.

The round constants of all of them are drawn from the Grain LFSR of `Hash.ZK.Grain`, initialised
with field type 1, S-box code 0, the field size in bits, the width and the round numbers: first
the `R_F/2 · t` constants of the initial external rounds, then the `R_P` internal constants,
then the `R_F/2 · t` constants of the final external rounds [HorizenLabs,
`poseidon2_rust_params.sage`]. Plonky3 releases before 0.6 drew the KoalaBear constants in a
different order (initial, final, internal); this library follows the corrected order of commit
`0056fa83`, which Plonky3 0.8.0 ships.

The module does not import Mathlib, so that the C exports of `HashFFI` can use it.

## References

* [Poseidon2] L. Grassi, D. Khovratovich, M. Schofnegger, *Poseidon2: A Faster Version of the
  Poseidon Hash Function*, AFRICACRYPT 2023; ePrint 2023/323. <https://eprint.iacr.org/2023/323>
* [HorizenLabs] The Poseidon2 reference implementation, commit 055bde3f.
  <https://github.com/HorizenLabs/poseidon2>
* [Plonky3] Plonky3 0.8.0. <https://github.com/Plonky3/Plonky3>
-/

@[expose] public section

namespace Hash.ZK.Poseidon2

open FieldOps

/-- The Grain samples of a Poseidon2 instance with field size `p` of `n` bits, width `t` and round
numbers `R_F`, `R_P`: the `R_F · t` external constants (initial rounds, then final rounds), and
the `R_P` internal constants. -/
def grainSamples (p n t RF RP : Nat) : List Nat × List Nat :=
  match Grain.sampleList p n (RF / 2 * t) (Grain.init ⟨1, 0, n, t, RF, RP⟩) with
  | (e₁, s) =>
    match Grain.sampleList p n RP s with
    | (i, s) =>
      match Grain.sampleList p n (RF / 2 * t) s with
      | (e₂, _) => (e₁ ++ e₂, i)

/-- A dyadic rational `±a / 2^b`, an entry of Plonky3's internal diagonals. -/
structure Dyadic where
  /-- Whether the value is negative. -/
  neg : Bool
  /-- The numerator `a`. -/
  num : Nat
  /-- The exponent `b` of the denominator `2^b`. -/
  exp : Nat

/-- `x / 2^b`, with `x` an integer. -/
def dy (x : Int) (b : Nat := 0) : Dyadic := ⟨x < 0, x.natAbs, b⟩

/-- The value of a dyadic rational in a field. -/
def Dyadic.toF {F : Type} [FieldOps F] (d : Dyadic) : F :=
  let x := mul (ofNat d.num) (inv (ofNat (2 ^ d.exp)))
  if d.neg then FieldOps.neg x else x

/-- Plonky3's `M₄ = circ(2, 3, 1, 1)`, by rows [Plonky3, `poseidon2/src/external.rs`,
`MDSMat4`]. -/
def plonky3M4 : List (List Nat) := [[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]]

/-- The diagonal `V` of BabyBear's width-16 internal matrix [Plonky3,
`BabyBearInternalLayerParameters`]. -/
def babyBearDiag16 : List Dyadic :=
  [dy (-2), dy 1, dy 2, dy 1 1, dy 3, dy 4, dy (-1) 1, dy (-3), dy (-4), dy 1 8, dy 1 2, dy 1 3,
    dy 1 27, dy (-1) 8, dy (-1) 4, dy (-1) 27]

/-- The diagonal `V` of BabyBear's width-24 internal matrix. -/
def babyBearDiag24 : List Dyadic :=
  [dy (-2), dy 1, dy 2, dy 1 1, dy 3, dy 4, dy (-1) 1, dy (-3), dy (-4), dy 1 8, dy 1 2, dy 1 3,
    dy 1 4, dy 1 7, dy 1 9, dy 1 27, dy (-1) 8, dy (-1) 2, dy (-1) 3, dy (-1) 4, dy (-1) 5,
    dy (-1) 6, dy (-1) 7, dy (-1) 27]

/-- The diagonal `V` of KoalaBear's width-16 internal matrix [Plonky3,
`KoalaBearInternalLayerParameters`]. -/
def koalaBearDiag16 : List Dyadic :=
  [dy (-2), dy 1, dy 2, dy 1 1, dy 3, dy 4, dy (-1) 1, dy (-3), dy (-4), dy 1 8, dy 1 3, dy 1 24,
    dy (-1) 8, dy (-1) 3, dy (-1) 4, dy (-1) 24]

/-- The diagonal `V` of KoalaBear's width-24 internal matrix. -/
def koalaBearDiag24 : List Dyadic :=
  [dy (-2), dy 1, dy 2, dy 1 1, dy 3, dy 4, dy (-1) 1, dy (-3), dy (-4), dy 1 8, dy 1 2, dy 1 3,
    dy 1 4, dy 1 5, dy 1 6, dy 1 24, dy (-1) 8, dy (-1) 3, dy (-1) 4, dy (-1) 5, dy (-1) 6,
    dy (-1) 7, dy (-1) 9, dy (-1) 24]

/-- A Plonky3 instance over a 31-bit prime field `p`: S-box exponent `α`, width `t`, `R_F = 8`,
`R_P` internal rounds, and internal diagonal `diag`. -/
structure Plonky3 where
  /-- The field size. -/
  p : Nat
  /-- The S-box exponent. -/
  α : Nat
  /-- The width. -/
  t : Nat
  /-- The number of internal rounds. -/
  RP : Nat
  /-- The internal diagonal. -/
  diag : List Dyadic

/-- BabyBear, width 16 [Plonky3, `default_babybear_poseidon2_16`]. -/
def babyBear16 : Plonky3 := ⟨babyBear, 7, 16, 13, babyBearDiag16⟩

/-- BabyBear, width 24 [Plonky3, `default_babybear_poseidon2_24`]. -/
def babyBear24 : Plonky3 := ⟨babyBear, 7, 24, 21, babyBearDiag24⟩

/-- KoalaBear, width 16 [Plonky3, `default_koalabear_poseidon2_16`]. -/
def koalaBear16 : Plonky3 := ⟨koalaBear, 3, 16, 20, koalaBearDiag16⟩

/-- KoalaBear, width 24 [Plonky3, `default_koalabear_poseidon2_24`]. -/
def koalaBear24 : Plonky3 := ⟨koalaBear, 3, 24, 23, koalaBearDiag24⟩

/-- The Grain samples of a Plonky3 instance (31-bit fields). -/
def Plonky3.samples (I : Plonky3) : List Nat × List Nat := grainSamples I.p 31 I.t 8 I.RP

/-- The parameters of a Plonky3 instance for the fast permutation, in a representation `F` of
the field. -/
def Plonky3.fastParams (I : Plonky3) (F : Type) [FieldOps F] : Fast.Params F I.t :=
  let (ce, ci) := I.samples
  ⟨I.α, 8, I.RP, (ce.map fun c => (ofNat c : F)).toArray, (ci.map fun c => (ofNat c : F)).toArray,
    .m4 (Vector.ofFn fun r => Vector.ofFn fun c =>
      ofNat ((plonky3M4.getD r.val []).getD c.val 0)),
    Vector.ofFn fun i => (I.diag.getD i.val (dy 0)).toF⟩

/-- The Grain samples of HorizenLabs' BN254 instance of width 3. -/
def hlBn254Samples : List Nat × List Nat := grainSamples bn254 254 3 8 56

/-- The parameters of HorizenLabs' BN254 instance of width 3 with the given samples. -/
def hlBn254FastParamsOf (F : Type) [FieldOps F] (samples : List Nat × List Nat) :
    Fast.Params F 3 :=
  ⟨5, 8, 56, (samples.1.map fun c => (ofNat c : F)).toArray,
    (samples.2.map fun c => (ofNat c : F)).toArray, .small,
    Vector.ofFn fun i => ofNat ([1, 1, 2].getD i.val 0)⟩

/-- The parameters of HorizenLabs' BN254 instance of width 3 for the fast permutation, in a
representation `F` of the field. -/
def hlBn254FastParams (F : Type) [FieldOps F] : Fast.Params F 3 :=
  hlBn254FastParamsOf F hlBn254Samples

/-! ### Maps between representations -/

variable {F G : Type} [FieldOps F] [FieldOps G] {f : F → G}

theorem Dyadic.map_toF (hf : Hom f) (d : Dyadic) : f d.toF = d.toF := by
  unfold Dyadic.toF
  cases d.neg <;> simp [hf.map_neg, hf.map_mul, hf.map_ofNat, hf.map_inv]

/-- A map preserving the operations maps the parameters in one representation to those in
another. -/
theorem Plonky3.map_fastParams (hf : Hom f) (I : Plonky3) :
    (I.fastParams F).map f = I.fastParams G := by
  unfold Plonky3.fastParams
  generalize I.samples = s
  rcases s with ⟨ce, ci⟩
  simp only [Fast.Params.map, Fast.External.map, List.map_toArray, List.map_map,
    Function.comp_def, hf.map_ofNat, Vector.map_ofFn, Dyadic.map_toF hf]

theorem map_hlBn254FastParamsOf (hf : Hom f) (samples : List Nat × List Nat) :
    (hlBn254FastParamsOf F samples).map f = hlBn254FastParamsOf G samples := by
  simp only [hlBn254FastParamsOf, Fast.Params.map, Fast.External.map, List.map_toArray,
    List.map_map, Function.comp_def, hf.map_ofNat, Vector.map_ofFn]

theorem map_hlBn254FastParams (hf : Hom f) :
    (hlBn254FastParams F).map f = hlBn254FastParams G :=
  map_hlBn254FastParamsOf hf _

end Hash.ZK.Poseidon2
