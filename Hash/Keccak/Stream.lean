/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Keccak.Fast

/-!
# Keccak: streaming interface

An incremental interface to the fast Keccak sponge: `State.init`, any number of `State.update`
calls, then `State.finalize` (or `State.squeezeBytes` for an extendable-output function). Full
blocks are absorbed as soon as they are available, and at most one partial block is buffered.

Hashing a message in pieces gives the same output as hashing it at once, for every output
length: `Hash.Keccak.Fast.State.squeezeBytes_updates` in `Hash.Keccak.StreamLemmas`. It is also
tested against the one-shot functions on every NIST CAVP message split at several points
(`HashKAT`), and by fuzzing with random splits (`harness/`).
-/

@[expose] public section

namespace Hash.Keccak.Fast

/-- The state of an incremental Keccak sponge computation. -/
structure State where
  /-- The rate in bytes. -/
  rate : Nat
  /-- The domain-separation byte. -/
  ds : UInt8
  /-- The default output length in bytes. -/
  outLen : Nat
  /-- The lanes, after absorbing the blocks so far. -/
  lanes : Array UInt64
  /-- The bytes not yet absorbed: fewer than one block. -/
  buf : ByteArray

namespace State

/-- The initial state of a sponge with the given rate, domain byte and default output length. -/
def init (rate : Nat) (ds : UInt8) (outLen : Nat) : State :=
  ⟨rate, ds, outLen, Array.replicate 25 0, ByteArray.empty⟩

/-- Absorb `n` consecutive blocks of `p`, starting at byte offset `off`. -/
def absorbBlocks (rate : Nat) (a : Array UInt64) (p : ByteArray) (off n : Nat) :
    Array UInt64 :=
  (List.range n).foldl (fun a i => absorbBlock rate a p (off + i * rate)) a

/-- Absorb more message bytes. -/
def update (s : State) (m : ByteArray) : State :=
  if s.buf.size + m.size < s.rate then
    { s with buf := s.buf ++ m }
  else
    -- Complete the buffered block (if any), then absorb whole blocks of `m` in place.
    let need := (s.rate - s.buf.size) % s.rate
    let a := if s.buf.size = 0 then s.lanes
      else absorbBlock s.rate s.lanes (s.buf ++ m.extract 0 need) 0
    let n := (m.size - need) / s.rate
    let a := absorbBlocks s.rate a m need n
    { s with lanes := a, buf := m.extract (need + n * s.rate) m.size }

/-- Pad the buffered bytes, absorb the final block, and squeeze `d` bytes. -/
def squeezeBytes (s : State) (d : Nat) : ByteArray :=
  let tail := pad s.rate s.ds s.buf
  let a := absorbBlocks s.rate s.lanes tail 0 (tail.size / s.rate)
  (squeeze s.rate a (max 1 ((d + s.rate - 1) / s.rate)) ByteArray.empty).extract 0 d

/-- Finish the computation, producing the default output length. -/
def finalize (s : State) : ByteArray := s.squeezeBytes s.outLen

end State

end Hash.Keccak.Fast
