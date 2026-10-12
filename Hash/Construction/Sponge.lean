/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Prelude.Bits

/-!
# The sponge construction

The sponge construction SPONGE[f, pad, r] of FIPS 202 §4 builds a function on bit strings with
output of any length from a permutation `f` of `b`-bit strings, a padding rule `pad` and a rate
`r < b` [Bertoni et al. 2007]. The message is padded, absorbed `r` bits at a time into the state,
and the output is squeezed out `r` bits at a time.

## References

* [FIPS 202] NIST, *SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions*,
  FIPS PUB 202, 2015. <https://doi.org/10.6028/NIST.FIPS.202>
* G. Bertoni, J. Daemen, M. Peeters, G. Van Assche, *Sponge Functions*, ECRYPT Hash Workshop,
  2007.
-/

@[expose] public section

namespace Hash.Sponge

/-- The multi-rate padding pad10*1: `1 ‖ 0^j ‖ 1` with `j = (−m − 2) mod x`, so that
`m + j + 2` is a positive multiple of `x` [FIPS 202, §5.1, Algorithm 9]. -/
def pad101 (x m : Nat) : List Bool :=
  [true] ++ List.replicate ((x - (m + 2) % x) % x) false ++ [true]

/-- The XOR of two bit strings of the same length. -/
def xorBits (a b : List Bool) : List Bool :=
  List.zipWith (· ^^ ·) a b

/-- Absorb the blocks `Ps` into the state `S`: `S ← f(S ⊕ (Pᵢ ‖ 0^c))` for each block
[FIPS 202, §4, Algorithm 8, step 6]. -/
def absorb (f : List Bool → List Bool) (c : Nat) (S : List Bool) (Ps : List (List Bool)) :
    List Bool :=
  Ps.foldl (fun S P => f (xorBits S (P ++ List.replicate c false))) S

/-- The first `k` output blocks: `Trunc_r(S)`, then `Trunc_r(f(S))`, and so on
[FIPS 202, §4, Algorithm 8, steps 7–10]. -/
def squeeze (f : List Bool → List Bool) (r : Nat) : List Bool → Nat → List Bool
  | _, 0 => []
  | S, k + 1 => S.take r ++ squeeze f r (f S) k

/-- SPONGE[f, pad, r](N, d) for a permutation `f` of `b`-bit strings: pad `N` to a multiple of
`r` bits, absorb it from the all-zero state, and squeeze until at least `d` bits are produced,
returning the first `d` [FIPS 202, §4, Algorithm 8].

Algorithm 8 squeezes one block, then continues while fewer than `d` bits have been produced; it
therefore produces `max 1 ⌈d / r⌉` blocks. -/
def sponge (f : List Bool → List Bool) (pad : Nat → Nat → List Bool) (b r : Nat)
    (N : List Bool) (d : Nat) : List Bool :=
  let P := N ++ pad r N.length
  let S := absorb f (b - r) (List.replicate b false) (chunks r P)
  (squeeze f r S (max 1 ((d + r - 1) / r))).take d

end Hash.Sponge
