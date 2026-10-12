/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import HashFFI.Poseidon
public import HashZK.Raw.Poseidon2

/-!
# C entry point for the Poseidon2 permutations

The permutations of `HashZK.Raw.Poseidon2`, whose agreement with the specifications is proved in
`HashZK.Raw.Poseidon2Equiv`; the byte encoding here is not.
-/

public section

namespace HashFFI

/-- `n` as `k` big-endian bytes (modulo `2^(8k)`). -/
def beBytes (k n : Nat) : ByteArray :=
  ⟨((List.range k).map fun i => (n >>> (8 * (k - 1 - i))).toUInt8).toArray⟩

/-- Apply a permutation of width `t` to `t` big-endian elements of `k` bytes each. -/
def permuteBytes (t k : Nat) (f : Vector Nat t → Vector Nat t) (input : ByteArray) : ByteArray :=
  if input.size ≠ t * k then ByteArray.empty else
  let out := f (Vector.ofFn fun i => beNat input (k * i.val) k)
  out.toList.foldl (fun acc x => acc ++ beBytes k x) ByteArray.empty

/-- A Poseidon2 permutation. The input is an instance byte, then the state: 0 to 3 for Plonky3's
BabyBear width 16 and 24 and KoalaBear width 16 and 24 (elements of 4 bytes), 4 for HorizenLabs'
BN254 width 3 (elements of 32 bytes); elements are big-endian and reduced modulo `p`. The output
is the permuted state in the same encoding. Returns the empty array on malformed input. -/
@[export hs_poseidon2] def poseidon2 (input : ByteArray) : ByteArray :=
  let state := input.extract 1 input.size
  match input.get! 0 with
  | 0 => permuteBytes 16 4 HashZK.Raw.Poseidon2.babyBear16 state
  | 1 => permuteBytes 24 4 HashZK.Raw.Poseidon2.babyBear24 state
  | 2 => permuteBytes 16 4 HashZK.Raw.Poseidon2.koalaBear16 state
  | 3 => permuteBytes 24 4 HashZK.Raw.Poseidon2.koalaBear24 state
  | 4 => permuteBytes 3 32 HashZK.Raw.Poseidon2.hlBn254 state
  | _ => ByteArray.empty

end HashFFI
