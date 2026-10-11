/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.SHA2.Fast

/-!
# SHA-2: streaming interface

An incremental interface to the fast specification: `State.init`, then any number of
`State.update` calls, then `State.finalize`. Full blocks are compressed as soon as they are
available, and at most one partial block is buffered.

Hashing a message in pieces gives the same digest as hashing it at once. This is tested against
the one-shot function on every NIST CAVP message split at several points (`HashKAT`), and by
fuzzing with random splits (`harness/`).
-/

@[expose] public section

namespace Hash.SHA2.Fast

open Word

/-- The state of an incremental SHA-2 computation. -/
structure State (α : Type) where
  /-- The member of the family being computed. -/
  P : Params
  /-- The round constants as machine words. -/
  K : Array α
  /-- The hash value after the blocks compressed so far. -/
  H : Array α
  /-- The bytes not yet compressed: fewer than one block. -/
  buf : ByteArray
  /-- The number of message bytes absorbed so far. -/
  len : Nat

namespace State

variable {α : Type} [Word α]

/-- The initial state for the member `P`. -/
def init (α : Type) [Word α] (P : Params) : State α where
  P := P
  K := (P.K.map ofNat).toArray
  H := (P.H0.map ofNat).toArray
  buf := ByteArray.empty
  len := 0

/-- Compress `n` consecutive blocks of `p`, starting at byte offset `off`. -/
@[specialize] def compressBlocks (P : Params) (K H : Array α) (p : ByteArray) (off n : Nat) :
    Array α :=
  (List.range n).foldl (fun H i => compress P K H p (off + i * (P.blockBits / 8))) H

/-- Absorb more message bytes. -/
@[specialize] def update (s : State α) (m : ByteArray) : State α :=
  let bb := s.P.blockBits / 8
  let len := s.len + m.size
  if s.buf.size + m.size < bb then
    { s with buf := s.buf ++ m, len }
  else
    -- Complete the buffered block (if any), then compress whole blocks of `m` in place.
    let need := (bb - s.buf.size) % bb
    let H := if s.buf.size = 0 then s.H
      else compress s.P s.K s.H (s.buf ++ m.extract 0 need) 0
    let n := (m.size - need) / bb
    let H := compressBlocks s.P s.K H m need n
    { s with H, buf := m.extract (need + n * bb) m.size, len }

/-- Pad the buffered bytes, compress the final block or blocks, and output the digest. -/
@[specialize] def finalize (s : State α) : ByteArray :=
  let bb := s.P.blockBits / 8
  let lengthBytes := s.P.lengthBits / 8
  let zeros := (bb - (s.len + 1 + lengthBytes) % bb) % bb
  let tail := s.buf.push 0x80 ++ ByteArray.zeros zeros ++ natToBytesBE lengthBytes (8 * s.len)
  let H := compressBlocks s.P s.K s.H tail 0 (tail.size / bb)
  (H.foldl pushBE ByteArray.empty).extract 0 (s.P.digestBits / 8)

end State

end Hash.SHA2.Fast
