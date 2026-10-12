/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Common.Sbox
public import Mathlib.Data.Matrix.Mul

/-!
# Poseidon2: reference specification

The Poseidon2 permutation [Poseidon2, §6] on states of `t` elements of a commutative ring `F` (in
practice a prime field `𝔽_p`):

`P₂(x) = E_{R_F−1} ∘ ⋯ ∘ E_{R_F/2} ∘ I_{R_P−1} ∘ ⋯ ∘ I_0 ∘ E_{R_F/2−1} ∘ ⋯ ∘ E_0 (M_E · x)`,

where an external round `E_r` adds a constant to every element, applies the S-box `x ↦ x ^ d` to
every element, and multiplies by the external matrix `M_E`, and an internal round `I_r` adds a
single constant to the first element, applies the S-box to it, and multiplies by the internal
matrix `M_I`. Unlike Poseidon, the permutation starts with a multiplication by `M_E`
[Poseidon2, §4], and the two kinds of round use different matrices [Poseidon2, §5].

The matrices are parameters. `externalSmall` and `blockCirculant` build the external matrices of
the paper and of the implementations, and `onesPlusDiag` the internal ones.

## References

* [Poseidon2] L. Grassi, D. Khovratovich, M. Schofnegger, *Poseidon2: A Faster Version of the
  Poseidon Hash Function*, AFRICACRYPT 2023; ePrint 2023/323 (revision of 2024-02-08).
  <https://eprint.iacr.org/2023/323>
-/

@[expose] public section

namespace Hash.ZK.Poseidon2

/-- The parameters of a Poseidon2 permutation [Poseidon2, §6]. -/
structure Params (F : Type*) (t : ℕ) where
  /-- The S-box exponent `d`. -/
  α : ℕ
  /-- The number of external rounds `R_F`, half before and half after the internal rounds. -/
  RF : ℕ
  /-- The number of internal rounds `R_P`. -/
  RP : ℕ
  /-- The constants `c^{(r)}` of external round `r < R_F`. -/
  CE : ℕ → Fin t → F
  /-- The constant `ĉ^{(r)}` of internal round `r < R_P`, added to the first element. -/
  CI : ℕ → F
  /-- The external matrix `M_E`. -/
  ME : Matrix (Fin t) (Fin t) F
  /-- The internal matrix `M_I`. -/
  MI : Matrix (Fin t) (Fin t) F

/-! ### Matrices -/

section Matrices

variable {F : Type*} [CommRing F]

/-- The matrix with every entry 1 except the diagonal, which is `1 + v_i`: `M_I` of
[Poseidon2, §5.2] with `μ_i = 1 + v_i`. -/
def onesPlusDiag {t : ℕ} (v : Fin t → F) : Matrix (Fin t) (Fin t) F :=
  fun i j => if i = j then 1 + v i else 1

/-- The external matrix of widths 2 and 3, `circ(2, 1)` and `circ(2, 1, 1)`: every entry 1
except the diagonal, which is 2. The paper sets `M_E = M_I` for these widths [Poseidon2, §6];
the reference implementation and every implementation in use take this matrix instead. -/
def externalSmall (t : ℕ) : Matrix (Fin t) (Fin t) F := onesPlusDiag fun _ => 1

/-- The external matrix `circ(2·M₄, M₄, …, M₄)` of a width that is a multiple of 4: block
`(a, b)` is `2·M₄` when `a = b` and `M₄` otherwise [Poseidon2, §5.1]. For width 4 the paper
takes `M₄` itself; the implementations covered here use only widths of 8 and above. -/
def blockCirculant {t : ℕ} (M4 : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin t) (Fin t) F :=
  fun i j =>
    (if i.val / 4 = j.val / 4 then 2 else 1) *
      M4 ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩ ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩

end Matrices

namespace Reference

variable {F : Type*} [CommRing F] {t : ℕ} (P : Params F t)

/-- External round `r`: add `c^{(r)}`, apply the S-box to every element, multiply by `M_E`
[Poseidon2, §6]. -/
def externalRound (s : Vector F t) (r : ℕ) : Vector F t :=
  Vector.ofFn (P.ME.mulVec fun i => sbox P.α (s[i] + P.CE r i))

/-- Internal round `r`: add `ĉ^{(r)}` to the first element, apply the S-box to it, multiply by
`M_I` [Poseidon2, §6]. -/
def internalRound (s : Vector F t) (r : ℕ) : Vector F t :=
  Vector.ofFn (P.MI.mulVec fun i => if i.val = 0 then sbox P.α (s[i] + P.CI r) else s[i])

/-- The Poseidon2 permutation [Poseidon2, §6]. -/
def permutation (s : Vector F t) : Vector F t :=
  let s := Vector.ofFn (P.ME.mulVec fun i => s[i])
  let s := (List.range (P.RF / 2)).foldl (externalRound P) s
  let s := (List.range P.RP).foldl (internalRound P) s
  (List.range (P.RF / 2)).foldl (fun s r => externalRound P s (P.RF / 2 + r)) s

end Reference

end Hash.ZK.Poseidon2
