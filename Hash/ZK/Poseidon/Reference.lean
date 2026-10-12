/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Common.Sbox
public import Mathlib.Data.Matrix.Mul

/-!
# Poseidon: reference specification

The Poseidon permutation [Poseidon, §2.2–2.3] on states of `t` elements of a commutative ring
`F` (in practice a prime field `𝔽_p`). It is a HADES design: `R_F / 2` full rounds, then `R_P`
partial rounds, then `R_F / 2` full rounds. Every round is

* `ARC`: add the round constants `c_r`,
* `SB`: apply the S-box `x ↦ x ^ α` to every element (full round) or to the first element only
  (partial round),
* `M`: multiply the state, as a column vector, by the matrix `M`,

in this order, including the last round [Poseidon, §2.2].

The specification is over any commutative ring so that it applies verbatim to `ZMod p` and to the
fast field representations of CompPoly; the parameters (constants, matrix, round numbers) are
data, and `Hash.ZK.Poseidon.Circom` derives the circomlib instances.

## References

* [Poseidon] L. Grassi, D. Khovratovich, C. Rechberger, A. Roy, M. Schofnegger, *Poseidon: A New
  Hash Function for Zero-Knowledge Proof Systems*, USENIX Security 2021; full version ePrint
  2019/458. <https://eprint.iacr.org/2019/458>
-/

@[expose] public section

namespace Hash.ZK.Poseidon

/-- The parameters of a Poseidon permutation [Poseidon, §2.2–2.3]. -/
structure Params (F : Type*) (t : ℕ) where
  /-- The S-box exponent `α`. -/
  α : ℕ
  /-- The number of full rounds `R_F`, half before and half after the partial rounds. -/
  RF : ℕ
  /-- The number of partial rounds `R_P`. -/
  RP : ℕ
  /-- The round constants `c_r` of round `r < R_F + R_P`. -/
  C : ℕ → Fin t → F
  /-- The linear layer: the state is multiplied by `M` as a column vector. -/
  M : Matrix (Fin t) (Fin t) F

namespace Reference

variable {F : Type*} [CommRing F] {t : ℕ} (P : Params F t)

/-- Round `r` is a full round when it is among the first or last `R_F / 2` rounds
[Poseidon, §2.2]. -/
def isFull (r : ℕ) : Bool := r < P.RF / 2 || P.RF / 2 + P.RP ≤ r

/-- The S-box layer of round `r`: every element in a full round, the first element in a partial
round [Poseidon, §2.2]. -/
def sboxLayer (r : ℕ) (s : Fin t → F) : Fin t → F :=
  fun i => if isFull P r || i.val = 0 then sbox P.α (s i) else s i

/-- Round `r`: `ARC`, then `SB`, then `M` [Poseidon, §2.2]. -/
def round (s : Vector F t) (r : ℕ) : Vector F t :=
  Vector.ofFn (P.M.mulVec (sboxLayer P r fun i => s[i] + P.C r i))

/-- The Poseidon permutation: `R_F + R_P` rounds [Poseidon, §2.2]. -/
def permutation (s : Vector F t) : Vector F t :=
  (List.range (P.RF + P.RP)).foldl (round P) s

/-! ### Ring homomorphisms -/

variable {G : Type*} [CommRing G]

/-- The parameters with constants and matrix mapped by `φ`. -/
def _root_.Hash.ZK.Poseidon.Params.map (φ : F →+* G) : Params G t :=
  ⟨P.α, P.RF, P.RP, fun r i => φ (P.C r i), P.M.map φ⟩

theorem map_sboxLayer (φ : F →+* G) (r : ℕ) (v : Fin t → F) :
    φ ∘ sboxLayer P r v = sboxLayer (P.map φ) r (φ ∘ v) := by
  funext j
  simp only [Function.comp, sboxLayer, show isFull (P.map φ) r = isFull P r from rfl]
  split_ifs <;> simp [map_sbox, Params.map]

/-- A ring homomorphism commutes with a round. -/
theorem map_round (φ : F →+* G) (s : Vector F t) (r : ℕ) :
    (round P s r).map φ = round (P.map φ) (s.map φ) r := by
  ext i hi
  simp only [round, Vector.getElem_map, Vector.getElem_ofFn]
  rw [RingHom.map_mulVec]
  congr 1
  rw [map_sboxLayer]
  congr 1
  funext j
  simp [Params.map]

/-- A ring homomorphism commutes with the permutation: computing in `F` and mapping to `G` is
computing in `G` with the mapped parameters. -/
theorem map_permutation (φ : F →+* G) (s : Vector F t) :
    (permutation P s).map φ = permutation (P.map φ) (s.map φ) := by
  unfold permutation
  change _ = List.foldl _ _ (List.range (P.RF + P.RP))
  generalize List.range (P.RF + P.RP) = rs
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, map_round]

end Reference

end Hash.ZK.Poseidon
