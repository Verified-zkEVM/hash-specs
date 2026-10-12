/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Common.Grain
public import Hash.ZK.Common.Primes
public import Hash.ZK.Poseidon.Fast

/-!
# Poseidon: the parameters of the circomlib instances

The round numbers and the Grain samples of circomlib's Poseidon instances over the BN254 scalar
field, for widths `t = 2 … 17`, and the parameters of the fast permutation built from them in any
representation of the field. `Hash.ZK.Poseidon.Circom` describes the derivation and states the
instances over `ZMod bn254`.

The module does not import Mathlib, so that the C exports of `HashFFI` can use it.

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

open FieldOps

/-- The number of partial rounds of circomlib's width-`t` instance, `t = 2 … 17`: the output of
the reference round-number script for 128-bit security, rounded up to a multiple of `t`
[circomlib, `N_ROUNDS_P`]. -/
def partialRounds (t : Nat) : Nat :=
  [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68].getD (t - 2) 0

/-- The Grain parameters of the width-`t` instance. -/
def grainParams (t : Nat) : Grain.Params := ⟨1, 0, 254, t, 8, partialRounds t⟩

/-- The `2t` samples `x₀ … x_{t−1}, y₀ … y_{t−1}` of the Cauchy matrix: distinct, with no
`x_i + y_j` divisible by `p`, drawn again otherwise [hadeshash]. -/
def cauchySeeds (p n t : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, s =>
    match Grain.rawList p n (2 * t) s with
    | (l, s) =>
      if l.Nodup ∧ ∀ i < t, ∀ j < t, (l.getD i 0 + l.getD (t + j) 0) % p ≠ 0 then l
      else cauchySeeds p n t fuel s

/-- The Grain samples of the width-`t` instance: the round constants, then the Cauchy seeds. -/
def samples (t : Nat) : List Nat × List Nat :=
  match Grain.sampleList bn254 254 ((8 + partialRounds t) * t) (Grain.init (grainParams t)) with
  | (cs, s) => (cs, cauchySeeds bn254 254 t 100 s)

/-- The parameters of circomlib's width-`t` instance for the fast permutation, in a representation
`F` of the field: the round constants, and the Cauchy matrix `M_{i,j} = 1 / (x_i + y_j)`. -/
def fastParams (F : Type) [FieldOps F] (t : Nat) : Fast.Params F t :=
  let (cs, xy) := samples t
  ⟨5, 8, partialRounds t, (cs.map fun c => (ofNat c : F)).toArray,
    Vector.ofFn fun i => Vector.ofFn fun j =>
      inv (ofNat (xy.getD i.val 0 + xy.getD (t + j.val) 0))⟩

/-- A map preserving the operations maps the parameters in one representation to those in
another. -/
theorem map_fastParams {F G : Type} [FieldOps F] [FieldOps G] {f : F → G} (hf : Hom f)
    (t : Nat) : (fastParams F t).map f = fastParams G t := by
  unfold fastParams
  rcases samples t with ⟨cs, xy⟩
  simp only [Fast.Params.map, List.map_toArray, List.map_map, Function.comp_def, hf.map_ofNat,
    Vector.map_ofFn, hf.map_inv]

end Hash.ZK.Poseidon.Circom
