/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Keccak.Constants
public import Hash.Prelude.Bytes

/-!
# Keccak: fast specification

An executable Keccak-f[1600] and Keccak sponge over byte arrays. The state is 25 lanes of 64
bits, `UInt64`, with lane `(x, y)` at index `x + 5y`; bit `z` of a lane is the state bit
`A[x, y, z]` of the reference (`Hash.Keccak.KeccakP`). The step mappings follow the reference one
by one, lane-wise instead of bit-wise.

Messages are byte arrays. Following FIPS 202, Appendix B.1, a byte holds eight consecutive
message bits, least significant first, so the domain-separation bits and the first padding bit
combine into one byte (`0x06` for SHA-3, `0x1F` for SHAKE, `0x01` for Keccak-256), and the last
padding bit is the top bit `0x80` of the last byte of the block.

`Hash.Keccak.Equiv` proves this equal to the reference on byte-aligned messages.
-/

@[expose] public section

namespace Hash.Keccak.Fast

/-- Lane `i` of the state, or 0 out of range. -/
@[inline] def lane (a : Array UInt64) (i : Nat) : UInt64 := a.getD i 0

/-- The array `#[f 0, …, f (n − 1)]`. (Built from a list, rather than with `Array.ofFn`, so that
the kernel can evaluate it in kernel-checked tests.) -/
@[inline] def tabulate (n : Nat) (f : Nat → UInt64) : Array UInt64 :=
  ((List.range n).map f).toArray

/-- θ, lane-wise: `C[x]` is the XOR of the five lanes of column `x`, and
`D[x] = C[x − 1] ⊕ rotl(C[x + 1], 1)` is XORed into every lane of column `x`. -/
def theta (a : Array UInt64) : Array UInt64 :=
  let c := tabulate 5 fun x =>
    lane a x ^^^ lane a (x + 5) ^^^ lane a (x + 10) ^^^ lane a (x + 15) ^^^ lane a (x + 20)
  let d := tabulate 5 fun x =>
    lane c ((x + 4) % 5) ^^^ UInt64.rotl (lane c ((x + 1) % 5)) 1
  tabulate 25 fun i => lane a i ^^^ lane d (i % 5)

/-- The ρ rotation amounts modulo 64, indexed by `x + 5y`. -/
def rhoRotations : Array UInt64 := (rhoOffsets.map fun n => (n % 64).toUInt64).toArray

/-- ρ, lane-wise: rotate lane `(x, y)` left by its offset. -/
def rho (a : Array UInt64) : Array UInt64 :=
  tabulate 25 fun i => UInt64.rotl (lane a i) (rhoRotations.getD i 0)

/-- π, lane-wise: the lane at `(x, y)` is the old lane at `((x + 3y) mod 5, x)`. -/
def pi (a : Array UInt64) : Array UInt64 :=
  tabulate 25 fun i =>
    let x := i % 5
    let y := i / 5
    lane a ((x + 3 * y) % 5 + 5 * x)

/-- χ, lane-wise: `A′[x, y] = A[x, y] ⊕ (¬A[x + 1, y] ∧ A[x + 2, y])`. -/
def chi (a : Array UInt64) : Array UInt64 :=
  tabulate 25 fun i =>
    let x := i % 5
    let y := i / 5
    lane a i ^^^ (~~~lane a ((x + 1) % 5 + 5 * y) &&& lane a ((x + 2) % 5 + 5 * y))

/-- The round constants of Keccak-f[1600] as words. -/
def roundConstantWords : Array UInt64 := (roundConstants.map (·.toUInt64)).toArray

/-- ι, lane-wise: XOR the round constant into lane `(0, 0)`. -/
def iota (a : Array UInt64) (ir : Nat) : Array UInt64 :=
  tabulate 25 fun i => if i = 0 then lane a 0 ^^^ roundConstantWords.getD ir 0 else lane a i

/-- One round of Keccak-f[1600]. -/
def round (a : Array UInt64) (ir : Nat) : Array UInt64 :=
  iota (chi (pi (rho (theta a)))) ir

/-- Keccak-f[1600] = Keccak-p[1600, 24], on 25 lanes. -/
def keccakF (a : Array UInt64) : Array UInt64 :=
  (List.range 24).foldl round a

/-- Pad a message to a whole number of `rate`-byte blocks: the byte `ds`, which holds the
domain-separation bits and the first bit of pad10*1, then zero bytes, with the last bit of
pad10*1 set in the last byte. -/
def pad (rate : Nat) (ds : UInt8) (m : ByteArray) : ByteArray :=
  let q := rate - m.size % rate
  if q = 1 then m.push (ds ||| 0x80)
  else (m.push ds ++ ByteArray.zeros (q - 2)).push 0x80

/-- XOR the block of `rate` bytes at offset `off` of `p` into the state, lane by lane in
little-endian order, and apply Keccak-f[1600]. -/
def absorbBlock (rate : Nat) (a : Array UInt64) (p : ByteArray) (off : Nat) : Array UInt64 :=
  keccakF <| tabulate 25 fun i =>
    if i < rate / 8 then lane a i ^^^ ByteArray.getUInt64LE p (off + 8 * i) else lane a i

/-- The first `rate` bytes of the state, lanes in little-endian order. -/
def rateBytes (rate : Nat) (a : Array UInt64) : ByteArray :=
  (List.range (rate / 8)).foldl (fun out i => ByteArray.pushUInt64LE out (lane a i))
    ByteArray.empty

/-- Squeeze `k` blocks of `rate` bytes, applying Keccak-f[1600] between blocks. -/
def squeeze (rate : Nat) : Array UInt64 → Nat → ByteArray → ByteArray
  | _, 0, out => out
  | a, k + 1, out => squeeze rate (keccakF a) k (out ++ rateBytes rate a)

/-- The Keccak sponge with a rate of `rate` bytes (a multiple of 8, less than 200) and
domain-separation byte `ds`, producing `d` bytes. -/
def sponge (rate : Nat) (ds : UInt8) (m : ByteArray) (d : Nat) : ByteArray :=
  let p := pad rate ds m
  let a := (List.range (p.size / rate)).foldl (fun a i => absorbBlock rate a p (i * rate))
    (Array.replicate 25 0)
  (squeeze rate a (max 1 ((d + rate - 1) / rate)) ByteArray.empty).extract 0 d

end Hash.Keccak.Fast
