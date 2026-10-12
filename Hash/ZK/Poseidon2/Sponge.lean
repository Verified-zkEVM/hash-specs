/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Construction.FieldSponge
public import Hash.ZK.Poseidon2.Instances

/-!
# Poseidon2: Plonky3's hash and compression

Plonky3 builds its Merkle-tree hash and compression functions from the Poseidon2 permutations: a
padding-free sponge (`Hash.FieldSponge.paddingFree`), typically of rate 8 and output 8 at width
16 and of rate 16 and output 8 at width 24, and a truncated-permutation compression
(`Hash.FieldSponge.truncatedPermutation`) of two chunks of 8 [Plonky3, `merkle-tree` and the
`*_poseidon2` benchmark configurations]. They are defined here for any rate, output and chunk.
-/

@[expose] public section

namespace Hash.ZK.Poseidon2

/-- Plonky3's padding-free sponge over a Poseidon2 instance, with the given rate and output
length. -/
def Plonky3.sponge (I : Plonky3) (rate out : ℕ) (xs : List (ZMod I.p)) : List (ZMod I.p) :=
  FieldSponge.paddingFree (FieldSponge.onList I.permutation) I.t rate out xs

/-- Plonky3's truncated-permutation compression over a Poseidon2 instance, keeping `chunk`
elements. -/
def Plonky3.compress (I : Plonky3) (chunk : ℕ) (inputs : List (List (ZMod I.p))) :
    List (ZMod I.p) :=
  FieldSponge.truncatedPermutation (FieldSponge.onList I.permutation) I.t chunk inputs

end Hash.ZK.Poseidon2
