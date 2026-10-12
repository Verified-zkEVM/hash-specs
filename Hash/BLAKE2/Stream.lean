/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.BLAKE2.Fast

/-!
# BLAKE2: streaming interface

An incremental interface to the fast BLAKE2: `State.init`, any number of `State.update` calls,
then `State.finalize`. BLAKE2 compresses the last block with the final flag set, so a block can
only be compressed once more input is known to follow it: the state buffers between one and
`bb` pending bytes once any input has arrived. The key block, if any, is the first pending block.

Hashing a message in pieces gives the same output as hashing it at once, for every key of at
most one block: `Hash.BLAKE2.Fast.State.finalize_updates` in `Hash.BLAKE2.StreamLemmas`. It is
also tested against the one-shot functions on every `blake2-kat.json` record split at several
points (`HashKAT`), and by fuzzing with random splits (`harness/`).
-/

@[expose] public section

namespace Hash.BLAKE2.Fast

open Word

/-- The state of an incremental BLAKE2 computation with words of type `α`. -/
structure State (α : Type) where
  /-- The parameters of the BLAKE2 instance. -/
  P : Params
  /-- The output length in bytes. -/
  nn : Nat
  /-- The chain value after the blocks compressed so far. -/
  h : Array α
  /-- The number of bytes compressed so far, including the key block. -/
  count : Nat
  /-- The pending bytes: at most one block, compressed once more input arrives or on
  `finalize`. -/
  buf : ByteArray

namespace State

variable {α : Type} [Word α]

/-- The initial state of BLAKE2 with the given key, salt, personalisation and output length. -/
def init (α : Type) [Word α] (P : Params) (key salt personal : ByteArray) (nn : Nat) : State α :=
  let pb := paramBlock P nn key.size salt personal
  let h : Array α := ((List.range 8).map fun i =>
    xor (ofNat (P.IV.getD i 0)) (loadLE pb (i * (P.w / 8)))).toArray
  let buf := if key.size = 0 then ByteArray.empty
    else key ++ ByteArray.zeros (P.blockBytes - key.size)
  ⟨P, nn, h, 0, buf⟩

/-- Add more message bytes. Every pending block followed by at least one more byte is
compressed. -/
def update (s : State α) (m : ByteArray) : State α :=
  let bb := s.P.blockBytes
  let p := s.buf ++ m
  -- Compress all whole blocks but the last pending byte's block.
  let n := (p.size - 1) / bb
  let h := (List.range n).foldl
    (fun h i => F s.P s.P.rounds h (block s.P p (i * bb)) (s.count + (i + 1) * bb) false) s.h
  { s with h, count := s.count + n * bb, buf := p.extract (n * bb) p.size }

/-- Zero-pad the pending bytes to a block, compress it as the final block, and output `nn`
bytes. -/
def finalize (s : State α) : ByteArray :=
  let bb := s.P.blockBytes
  let last := s.buf ++ ByteArray.zeros (bb - s.buf.size)
  let h := F s.P s.P.rounds s.h (block s.P last 0) (s.count + s.buf.size) true
  (h.foldl pushLE ByteArray.empty).extract 0 s.nn

end State

end Hash.BLAKE2.Fast
