/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Common.Grain
public import Hash.ZK.Common.Primes
public import Hash.ZK.Poseidon.Reference
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

/-- The number of partial rounds of circomlib's width-`t` instance, `t = 2 … 17`: the output of
the reference round-number script for 128-bit security, rounded up to a multiple of `t`
[circomlib, `N_ROUNDS_P`]. -/
def partialRounds (t : ℕ) : ℕ :=
  [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68].getD (t - 2) 0

/-- The Grain parameters of the width-`t` instance. -/
def grainParams (t : ℕ) : Grain.Params := ⟨1, 0, 254, t, 8, partialRounds t⟩

/-- The `2t` samples `x₀ … x_{t−1}, y₀ … y_{t−1}` of the Cauchy matrix: distinct, with no
`x_i + y_j` divisible by `p`, drawn again otherwise [hadeshash]. -/
def cauchySeeds (p n t : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, s =>
    match Grain.rawList p n (2 * t) s with
    | (l, s) =>
      if l.Nodup ∧ ∀ i < t, ∀ j < t, (l.getD i 0 + l.getD (t + j) 0) % p ≠ 0 then l
      else cauchySeeds p n t fuel s

/-- The Grain samples of the width-`t` instance: the round constants, then the Cauchy seeds. -/
def samples (t : ℕ) : List ℕ × List ℕ :=
  match Grain.sampleList bn254 254 ((8 + partialRounds t) * t) (Grain.init (grainParams t)) with
  | (cs, s) => (cs, cauchySeeds bn254 254 t 100 s)

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

end Hash.ZK.Poseidon.Circom
