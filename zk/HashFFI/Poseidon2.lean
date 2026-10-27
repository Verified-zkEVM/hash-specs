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

/-- The 31-bit Poseidon2 permutation with the given instance byte and its width. -/
def perm31 : UInt8 → Option (Σ t : Nat, (Vector Nat t → Vector Nat t))
  | 0 => some ⟨16, HashZK.Raw.Poseidon2.babyBear16⟩
  | 1 => some ⟨24, HashZK.Raw.Poseidon2.babyBear24⟩
  | 2 => some ⟨16, HashZK.Raw.Poseidon2.koalaBear16⟩
  | 3 => some ⟨24, HashZK.Raw.Poseidon2.koalaBear24⟩
  | _ => none

/-- Big-endian 4-byte elements from offset `off`. -/
def words (b : ByteArray) (off : Nat) : List Nat :=
  (List.range ((b.size - off) / 4)).map fun i => beNat b (off + 4 * i) 4

/-- Plonky3's padding-free sponge over a 31-bit Poseidon2 permutation. The input is the instance
byte (0 to 3, as for `poseidon2`), the rate, the output length, then the elements (4 bytes each,
big-endian). Returns the empty array on malformed input, or when the parameters are outside
Plonky3's bounds (`0 < rate < t`, `0 < out ≤ rate`). -/
@[export hs_poseidon2_sponge] def poseidon2Sponge (input : ByteArray) : ByteArray :=
  match perm31 (input.get! 0) with
  | some ⟨t, f⟩ =>
    let rate := (input.get! 1).toNat
    let out := (input.get! 2).toNat
    if input.size < 3 ∨ (input.size - 3) % 4 ≠ 0 ∨ rate = 0 ∨ t ≤ rate ∨ out = 0 ∨ rate < out then
      ByteArray.empty
    else
      (HashZK.Raw.Poseidon2.sponge f rate out (words input 3)).foldl
        (fun acc x => acc ++ beBytes 4 x) ByteArray.empty
  | none => ByteArray.empty

/-- Plonky3's truncated-permutation compression over a 31-bit Poseidon2 permutation. The input is
the instance byte, the chunk length, then the chunks' elements (4 bytes each, big-endian); the
output is the first `chunk` elements. Returns the empty array on malformed input, or when the
chunks do not fit in the state. -/
@[export hs_poseidon2_compress] def poseidon2Compress (input : ByteArray) : ByteArray :=
  match perm31 (input.get! 0) with
  | some ⟨t, f⟩ =>
    let chunk := (input.get! 1).toNat
    let xs := words input 2
    if input.size < 2 ∨ (input.size - 2) % 4 ≠ 0 ∨ chunk = 0 ∨ xs.length % chunk ≠ 0 ∨
        t < xs.length ∨ xs.isEmpty then
      ByteArray.empty
    else
      (HashZK.Raw.Poseidon2.compress f chunk (Hash.chunks chunk xs)).foldl
        (fun acc x => acc ++ beBytes 4 x) ByteArray.empty
  | none => ByteArray.empty

end HashFFI
