/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import HashZK.Raw.Poseidon

/-!
# C entry points for the ZK-friendly hashes

Field elements cross the boundary as 32-byte big-endian integers. The functions compute on the
raw Montgomery limbs of `HashZK.Raw`, whose agreement with the specifications is proved in
`HashZK.Raw.Equiv` (for Poseidon, `HashZK.Raw.Poseidon.poseidonNat_eq`); the byte encoding here
is not.
-/

public section

namespace HashFFI

/-- The big-endian integer of `k` bytes of `b` from offset `off`. -/
def beNat (b : ByteArray) (off k : Nat) : Nat :=
  (List.range k).foldl (fun acc i => 256 * acc + (b.get! (off + i)).toNat) 0

/-- `n` as 32 big-endian bytes (modulo `2²⁵⁶`). -/
def be32 (n : Nat) : ByteArray :=
  ⟨((List.range 32).map fun i => (n >>> (8 * (31 - i))).toUInt8).toArray⟩

/-- circomlib's Poseidon over BN254. The input is one to sixteen 32-byte big-endian field
elements, reduced modulo `p`; the output is 32 bytes. Returns the empty array on malformed input. -/
@[export hs_poseidon_circom] def poseidonCircom (input : ByteArray) : ByteArray :=
  let n := input.size / 32
  if input.size % 32 ≠ 0 ∨ n = 0 ∨ 16 < n then ByteArray.empty else
  be32 (HashZK.Raw.Poseidon.poseidonNat ((Array.range n).map fun i => beNat input (32 * i) 32))

end HashFFI
