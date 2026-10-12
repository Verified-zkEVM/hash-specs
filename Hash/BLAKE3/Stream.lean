/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.BLAKE3.Fast

/-!
# BLAKE3: streaming interface

An incremental interface to the fast BLAKE3: `State.init`, any number of `State.update` calls,
then `State.finalize`. It follows [BLAKE3, §5.1]: complete chunks are added to the stack of
chaining values of `Hash.Construction.Tree` as soon as at least one more byte arrives, and the
current chunk, between 1 and 1024 bytes once any input has arrived, is buffered.

`Hash.BLAKE3.Stream.finalize_updates` proves that hashing a message in pieces gives the same
output as hashing it at once.
-/

@[expose] public section

namespace Hash.BLAKE3.Fast

/-- The state of an incremental BLAKE3 computation. -/
structure State where
  /-- The key words. -/
  key : Array UInt32
  /-- The mode flags. -/
  flags : Nat
  /-- The chaining values of complete subtrees, newest first. -/
  stack : List (Array UInt32)
  /-- The number of chunks added to the stack. -/
  count : Nat
  /-- The current chunk: at most 1024 bytes. -/
  buf : ByteArray

namespace State

/-- The initial state with the given key words and mode flags. -/
def init (key : Array UInt32) (flags : Nat) : State := ⟨key, flags, [], 0, ByteArray.empty⟩

/-- The complete chunks of `p` that are followed by at least one more byte. -/
def fullChunks (p : ByteArray) : List ByteArray :=
  (List.range ((p.size - 1) / CHUNK_LEN)).map fun j =>
    p.extract (j * CHUNK_LEN) ((j + 1) * CHUNK_LEN)

/-- Add more input bytes. -/
def update (s : State) (m : ByteArray) : State :=
  let p := s.buf ++ m
  let n := (p.size - 1) / CHUNK_LEN
  { s with
    stack := Tree.pushAll (chunkOutput s.key s.flags) (parentOutput s.key s.flags)
      Output.chainingValue s.stack s.count (fullChunks p)
    count := s.count + n
    buf := p.extract (n * CHUNK_LEN) p.size }

/-- The root node: the current chunk merged with every entry of the stack. -/
def rootOutput (s : State) : Output :=
  Tree.finish (parentOutput s.key s.flags) Output.chainingValue s.stack
    (chunkOutput s.key s.flags s.count s.buf)

/-- Finish the computation, producing `d` bytes of output. -/
def finalize (s : State) (d : Nat) : ByteArray := s.rootOutput.rootBytes d

end State

end Hash.BLAKE3.Fast
