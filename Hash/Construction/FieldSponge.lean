/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Prelude.Bits

/-!
# Sponges and compression over field elements

The ways the ZK-friendly permutations are turned into hash functions on field elements. Each
ecosystem has its own conventions, and each is a separate definition here:

* *Plonky3's padding-free sponge* (`paddingFree`) [Plonky3, `PaddingFreeSponge`]: from the zero
  state, each block of `rate` input elements overwrites the start of the state, which is then
  permuted; a final partial block overwrites only its own positions, and an empty final block
  is not absorbed. The digest is the first `out` elements of the state. There is no padding, so
  it is collision resistant only for inputs of a fixed length (Merkle leaves, trace rows).
* *Plonky3's truncated permutation* (`truncatedPermutation`) [Plonky3, `TruncatedPermutation`]:
  a 2-to-1 (or `n`-to-1) compression for Merkle trees that places the inputs at the start of
  the zero state, permutes, and keeps the first `chunk` elements.
* *circomlib's one-shot hash* is `Hash.ZK.Poseidon.Circom.poseidonEx`: one permutation of
  `[initState, inputs]`, with the capacity element initialised by the caller.

`Hash.FieldSponge.absorb_append` proves that absorbing a block-aligned prefix and then the rest
gives the state of absorbing everything, so an incremental implementation agrees with the
one-shot definition. The module does not import Mathlib, so that the C exports can use it.

## References

* [Plonky3] Plonky3 0.8.0, `symmetric/src/sponge.rs` and `symmetric/src/compression.rs`.
  <https://github.com/Plonky3/Plonky3>
* G. Bertoni, J. Daemen, M. Peeters, G. Van Assche, *Sponge Functions*, ECRYPT Hash Workshop,
  2007.
-/

@[expose] public section

namespace Hash.FieldSponge

variable {α : Type} [Inhabited α]

/-- Overwrite the start of the state with a block. -/
def overwrite (block state : List α) : List α := block ++ state.drop block.length

/-- Absorb blocks in overwrite mode: each block overwrites the start of the state, which is then
permuted [Plonky3, `PaddingFreeSponge::hash_iter`]. -/
def absorb (perm : List α → List α) (state : List α) (blocks : List (List α)) : List α :=
  blocks.foldl (fun s b => perm (overwrite b s)) state

/-- Plonky3's padding-free sponge: absorb the input in blocks of `rate` elements from the zero
state of `width` elements, and output the first `out` elements [Plonky3,
`PaddingFreeSponge`]. -/
def paddingFree (perm : List α → List α) (width rate out : Nat) (xs : List α) : List α :=
  (absorb perm (List.replicate width default) (chunks rate xs)).take out

/-- Plonky3's truncated permutation: place the inputs at the start of the zero state of `width`
elements, permute, and keep the first `chunk` elements [Plonky3, `TruncatedPermutation`]. -/
def truncatedPermutation (perm : List α → List α) (width chunk : Nat) (inputs : List (List α)) :
    List α :=
  (perm (inputs.flatten ++ List.replicate (width - inputs.flatten.length) default)).take chunk

/-- A permutation of vectors as a function on lists: the list is cut or padded with the default
element to the width. -/
def onList {t : Nat} (perm : Vector α t → Vector α t) (l : List α) : List α :=
  (perm (Vector.ofFn fun i => l.getD i.val default)).toList

end Hash.FieldSponge
