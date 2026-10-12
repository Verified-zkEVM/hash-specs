/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Keccak.KeccakP

/-!
# Keccak constants

The ρ offsets and the round constants of Keccak-f[1600], written as tables in the form usually
printed (for example in [FIPS 202, Table 2] and in the Keccak reference), and proved equal to
their definitions in `Hash.Keccak.KeccakP` by kernel computation. The fast specification uses
these tables.

## References

* [FIPS 202] NIST, *SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions*,
  FIPS PUB 202, 2015. <https://doi.org/10.6028/NIST.FIPS.202>
* G. Bertoni, J. Daemen, M. Peeters, G. Van Assche, *The Keccak Reference*, version 3.0, 2011.
  <https://keccak.team/files/Keccak-reference-3.0.pdf>
-/

@[expose] public section

namespace Hash.Keccak

/-- The ρ offsets, indexed by `x + 5y` [FIPS 202, Table 2]. -/
def rhoOffsets : List Nat :=
  [  0,   1, 190,  28,  91,
    36, 300,   6,  55, 276,
     3,  10, 171, 153, 231,
   105,  45,  15,  21, 136,
   210,  66, 253, 120,  78]

/-- The round constants of Keccak-f[1600], as 64-bit numbers whose bit `z` is `RC[z]`
[Keccak reference, Table 1.1]. -/
def roundConstants : List Nat :=
  [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
   0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
   0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
   0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
   0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
   0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The ρ offset table is the offsets of Algorithm 2. -/
theorem rhoOffsets_eq :
    rhoOffsets = (List.finRange 25).map fun i =>
      ρOffset ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩ ⟨i.val / 5, by omega⟩ := by
  decide +kernel

/-- The round-constant table is the constants of Algorithm 6 for `w = 64`. -/
theorem roundConstants_eq :
    roundConstants = (List.range 24).map fun ir =>
      ((List.range 64).map fun z => if RC 6 (ir : Nat) z then 2 ^ z else 0).sum := by
  decide +kernel

end Hash.Keccak
