/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.SHA2.API
public import Hash.Keccak.API

/-!
# C entry points for the differential-testing harness

Each function takes and returns a `ByteArray` and is exported under a stable C symbol name, so
that the Rust harness in `harness/` can call the fast specifications in-process. This library
must stay Mathlib-free: it is linked into the harness as a static library together with Lean's
runtime, and importing Mathlib would make that library enormous.

`hs_sha2_stream` exposes the streaming interface for testing: it hashes a message in pieces of
given sizes, so the harness can check that every way of splitting a message gives the same digest.

Arguments are owned (exported functions cannot take borrowed parameters), so the caller passes
one reference to the input, which the callee consumes.
-/

public section

namespace HashFFI

/-- SHA-224. -/
@[export hs_sha224] def sha224 (m : ByteArray) : ByteArray := Hash.sha224 m
/-- SHA-256. -/
@[export hs_sha256] def sha256 (m : ByteArray) : ByteArray := Hash.sha256 m
/-- SHA-384. -/
@[export hs_sha384] def sha384 (m : ByteArray) : ByteArray := Hash.sha384 m
/-- SHA-512. -/
@[export hs_sha512] def sha512 (m : ByteArray) : ByteArray := Hash.sha512 m
/-- SHA-512/224. -/
@[export hs_sha512t224] def sha512t224 (m : ByteArray) : ByteArray := Hash.sha512t224 m
/-- SHA-512/256. -/
@[export hs_sha512t256] def sha512t256 (m : ByteArray) : ByteArray := Hash.sha512t256 m
/-- SHA3-224. -/
@[export hs_sha3x224] def sha3x224 (m : ByteArray) : ByteArray := Hash.sha3x224 m
/-- SHA3-256. -/
@[export hs_sha3x256] def sha3x256 (m : ByteArray) : ByteArray := Hash.sha3x256 m
/-- SHA3-384. -/
@[export hs_sha3x384] def sha3x384 (m : ByteArray) : ByteArray := Hash.sha3x384 m
/-- SHA3-512. -/
@[export hs_sha3x512] def sha3x512 (m : ByteArray) : ByteArray := Hash.sha3x512 m
/-- Keccak-256. -/
@[export hs_keccak256] def keccak256 (m : ByteArray) : ByteArray := Hash.keccak256 m

/-- Split an XOF input into the output length (the first four bytes, big-endian) and the
message (the rest). -/
def xofInput (input : ByteArray) : Nat × ByteArray :=
  let d := (List.range 4).foldl (fun d i => 256 * d + (input.get! i).toNat) 0
  (d, input.extract 4 input.size)

/-- SHAKE128. The input is the output length in bytes (four bytes, big-endian), then the
message. -/
@[export hs_shake128] def shake128 (input : ByteArray) : ByteArray :=
  let (d, m) := xofInput input
  Hash.shake128 m d
/-- SHAKE256, with input as for `shake128`. -/
@[export hs_shake256] def shake256 (input : ByteArray) : ByteArray :=
  let (d, m) := xofInput input
  Hash.shake256 m d

/-- Absorb `m` into `s` in pieces whose sizes cycle through `sizes` (a size of 0 is an empty
update), then finalize. -/
def streamPieces {α : Type} [Hash.SHA2.Fast.Word α] (s : Hash.SHA2.Fast.State α)
    (sizes : List Nat) (m : ByteArray) : ByteArray := Id.run do
  let mut s := s
  let mut off := 0
  let mut i := 0
  -- If every size were 0 the loop would never advance, so fall back to single bytes.
  let sizes := if sizes.all (· == 0) then [1] else sizes
  while off < m.size do
    let n := sizes.getD (i % sizes.length) 1
    s := s.update (m.extract off (off + n))
    off := off + n
    i := i + 1
  return s.finalize

/-- The streaming interface, for testing. The input is a variant byte (0–5 for SHA-224, SHA-256,
SHA-384, SHA-512, SHA-512/224, SHA-512/256), a count `k`, `k` big-endian 16-bit piece sizes, and
then the message. Returns the empty array on malformed input. -/
@[export hs_sha2_stream] def sha2Stream (input : ByteArray) : ByteArray :=
  let k := (input.get! 1).toNat
  if input.size < 2 + 2 * k then ByteArray.empty else
  let sizes := (List.range k).map fun j =>
    256 * (input.get! (2 + 2 * j)).toNat + (input.get! (3 + 2 * j)).toNat
  let m := input.extract (2 + 2 * k) input.size
  match (input.get! 0).toNat with
  | 0 => streamPieces Hash.sha224Init sizes m
  | 1 => streamPieces Hash.sha256Init sizes m
  | 2 => streamPieces Hash.sha384Init sizes m
  | 3 => streamPieces Hash.sha512Init sizes m
  | 4 => streamPieces Hash.sha512t224Init sizes m
  | 5 => streamPieces Hash.sha512t256Init sizes m
  | _ => ByteArray.empty

end HashFFI
