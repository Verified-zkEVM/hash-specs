/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.BLAKE2.Fast
public import Hash.BLAKE2.Stream

/-!
# BLAKE2: byte-level API

BLAKE2b, BLAKE2s and Ethereum's BLAKE2b `F` precompile on byte arrays, computed by the fast
specification.
-/

@[expose] public section

namespace Hash

/-- BLAKE2b with an `nn`-byte output (1 to 64), a key of at most 64 bytes, and a salt and
personalisation string of at most 16 bytes each [RFC 7693; BLAKE2, §2.5]. -/
def blake2bWith (key salt personal : ByteArray) (nn : Nat) (m : ByteArray) : ByteArray :=
  BLAKE2.Fast.hashWith UInt64 BLAKE2.blake2bParams key salt personal nn m

/-- BLAKE2s with an `nn`-byte output (1 to 32), a key of at most 32 bytes, and a salt and
personalisation string of at most 8 bytes each [RFC 7693; BLAKE2, §2.5]. -/
def blake2sWith (key salt personal : ByteArray) (nn : Nat) (m : ByteArray) : ByteArray :=
  BLAKE2.Fast.hashWith UInt32 BLAKE2.blake2sParams key salt personal nn m

/-- BLAKE2b-512, unkeyed [RFC 7693]. -/
def blake2b (m : ByteArray) : ByteArray := blake2bWith .empty .empty .empty 64 m

/-- BLAKE2s-256, unkeyed [RFC 7693]. -/
def blake2s (m : ByteArray) : ByteArray := blake2sWith .empty .empty .empty 32 m

/-- The initial streaming state of `blake2bWith key salt personal nn`. -/
def blake2bInit (key salt personal : ByteArray) (nn : Nat) : BLAKE2.Fast.State UInt64 :=
  .init UInt64 BLAKE2.blake2bParams key salt personal nn

/-- The initial streaming state of `blake2sWith key salt personal nn`. -/
def blake2sInit (key salt personal : ByteArray) (nn : Nat) : BLAKE2.Fast.State UInt32 :=
  .init UInt32 BLAKE2.blake2sParams key salt personal nn

/-- The BLAKE2b compression function `F` with any number of rounds [EIP-152]. -/
def blake2bF (rounds : Nat) (h m : Array UInt64) (t0 t1 : UInt64) (f : Bool) : Array UInt64 :=
  BLAKE2.Fast.F BLAKE2.blake2bParams rounds h m (t0.toNat + 2 ^ 64 * t1.toNat) f

/-- Ethereum's BLAKE2b `F` precompile at address `0x09` [EIP-152]. The input is exactly 213
bytes: the number of rounds (4 bytes, big-endian), the state `h` (8 words), the message block
`m` (16 words), the offset counters `t₀, t₁` (2 words), all little-endian 64-bit words, and the
final-block flag `f` (one byte, 0 or 1). The output is the new state, 64 bytes. -/
def blake2bPrecompile (input : ByteArray) : Except String ByteArray := do
  if input.size != 213 then
    throw "input length for BLAKE2 F precompile should be exactly 213 bytes"
  let f := input.get! 212
  if f > 1 then throw "incorrect final block indicator flag"
  let rounds := (List.range 4).foldl (fun r i => 256 * r + (input.get! i).toNat) 0
  let word (i : Nat) := ByteArray.getUInt64LE input (4 + 8 * i)
  let h := ((List.range 8).map word).toArray
  let m := ((List.range 16).map fun i => word (8 + i)).toArray
  let out := blake2bF rounds h m (word 24) (word 25) (f == 1)
  return out.foldl ByteArray.pushUInt64LE ByteArray.empty

end Hash
