/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Poseidon.CircomParams
public import Hash.ZK.Poseidon.Equiv
public import Mathlib.Data.ZMod.Basic

/-!
# Poseidon: the circomlib instances over BN254

The Poseidon instances of circomlib [circomlib] over the BN254 scalar field, for widths
`t = 2 … 17` (one to sixteen inputs): `α = 5`, `R_F = 8`, and `R_P` from `partialRounds`.

Their constants are not tables but derived, as circomlib's were: the round constants and then the
Cauchy matrix are drawn from the Grain LFSR initialised with field type 1, S-box code 0, `n = 254`,
the width and the round numbers, exactly as by the reference script invoked as
`sage generate_parameters_grain.sage 1 0 254 t 8 R_P p` [hadeshash; Poseidon, App. E]:

* `(R_F + R_P) · t` round constants, each a 254-bit sample below `p`; constant `r · t + i` is
  added to element `i` in round `r`;
* `2t` further 254-bit samples reduced modulo `p`, drawn again until they are distinct and no
  `x_i + y_j` is zero; the matrix is `M_{i,j} = 1 / (x_i + y_j)` [Poseidon, §2.3].

The reference script also checks the matrix against infinitely long subspace trails and samples
again on failure [Poseidon, §2.3]; the first sample passes for every circomlib width, which the
comparison with circomlib's published constants confirms, so the check is not repeated here.

circomlib hashes `n` inputs with the width-`n + 1` permutation applied once to
`[initState, x₁, …, x_n]`, and outputs the first `nOut` elements (by default `initState = 0` and
one output) [circomlib, `poseidon.circom`]. There is no padding or domain separation, unlike the
sponge of [Poseidon, §4.2].

## References

* [Poseidon] L. Grassi, D. Khovratovich, C. Rechberger, A. Roy, M. Schofnegger, *Poseidon: A New
  Hash Function for Zero-Knowledge Proof Systems*, USENIX Security 2021; full version ePrint
  2019/458. <https://eprint.iacr.org/2019/458>
* [hadeshash] The Poseidon reference implementation, commit 208b5a16.
  <https://extgit.iaik.tugraz.at/krypto/hadeshash>
* [circomlib] iden3, `circuits/poseidon.circom` and `circomlibjs/src/poseidon_reference.js`,
  commits 35e54ea2 and 48b3ab37. <https://github.com/iden3/circomlib>
-/

@[expose] public section

namespace Hash.ZK.Poseidon.Circom

/-- The parameters of circomlib's width-`t` Poseidon over `ZMod bn254`. -/
def params (t : ℕ) : Params (ZMod bn254) t :=
  let (cs, xy) := samples t
  { α := 5
    RF := 8
    RP := partialRounds t
    C := fun r i => (cs.getD (r * t + i.val) 0 : ZMod bn254)
    M := fun i j => ((xy.getD i.val 0 + xy.getD (t + j.val) 0 : ℕ) : ZMod bn254)⁻¹ }

/-- circomlib's `PoseidonEx`: hash the `n` inputs with the width-`n + 1` permutation and initial
capacity element `initState`, and output the first `nOut` elements [circomlib]. -/
def poseidonEx (n : ℕ) (initState : ZMod bn254) (inputs : Fin n → ZMod bn254) (nOut : ℕ) :
    List (ZMod bn254) :=
  (Reference.permutation (params (n + 1)) (Vector.ofFn (Fin.cons initState inputs))).toList.take
    nOut

/-- circomlib's `Poseidon(n)`: the first output element, with initial capacity element 0
[circomlib]. -/
def poseidon (n : ℕ) (inputs : Fin n → ZMod bn254) : ZMod bn254 :=
  (Reference.permutation (params (n + 1)) (Vector.ofFn (Fin.cons 0 inputs)))[0]

/-- Over `ZMod bn254`, the fast parameters (`Hash.ZK.Poseidon.Circom.fastParams`) are the
circomlib parameters. -/
theorem fastParams_toRef (t : ℕ) : (fastParams (ZMod bn254) t).toRef = params t := by
  unfold fastParams params
  rcases samples t with ⟨cs, xy⟩
  simp only [Fast.Params.toRef, Vector.getElem_ofFn, Fin.getElem_fin, FieldOps.ofNat_eq,
    FieldOps.inv_eq]
  congr
  funext r i
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  cases cs[r * t + i.val]? <;> simp

/-- The fast permutation, with the fast parameters in any representation `F` of the field,
computes circomlib's permutation through a map `f : F → ZMod bn254` that preserves the
operations. -/
theorem map_permutation_fastParams {F : Type} [FieldOps F] {f : F → ZMod bn254}
    (hf : FieldOps.Hom f) (t : ℕ) (s : Vector F t) :
    (Fast.permutation (fastParams F t) s).map f = Reference.permutation (params t) (s.map f) := by
  rw [Fast.map_permutation _ hf, map_fastParams hf, Fast.permutation_eq, fastParams_toRef]

end Hash.ZK.Poseidon.Circom
