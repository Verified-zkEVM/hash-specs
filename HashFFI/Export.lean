/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.SHA2.API
public import Hash.Keccak.API
public import Hash.BLAKE2.API
public import Hash.BLAKE3.API

/-!
# C entry points for the differential-testing harness

Each function takes and returns a `ByteArray` and is exported under a stable C symbol name, so
that the Rust harness in `harness/` can call the fast specifications in-process. This library
must stay Mathlib-free: it is linked into the harness as a static library together with Lean's
runtime, and importing Mathlib would make that library enormous.

`hs_sha2_stream`, `hs_keccak_stream`, `hs_blake2_stream` and `hs_blake3_stream` expose the streaming interfaces for
testing: it hashes a message in pieces of
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

/-- Absorb `m` into the Keccak state `s` in pieces whose sizes cycle through `sizes`, then
squeeze `d` bytes. -/
def keccakStreamPieces (s : Hash.Keccak.Fast.State) (sizes : List Nat) (m : ByteArray)
    (d : Nat) : ByteArray := Id.run do
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
  return s.squeezeBytes d

/-- The Keccak streaming interface, for testing. The input is a variant byte (0–6 for SHA3-224,
SHA3-256, SHA3-384, SHA3-512, SHAKE128, SHAKE256, Keccak-256), a count `k`, `k` big-endian 16-bit
piece sizes, a big-endian 16-bit output length (used by SHAKE only), and then the message.
Returns the empty array on malformed input. -/
@[export hs_keccak_stream] def keccakStream (input : ByteArray) : ByteArray :=
  let k := (input.get! 1).toNat
  if input.size < 4 + 2 * k then ByteArray.empty else
  let sizes := (List.range k).map fun j =>
    256 * (input.get! (2 + 2 * j)).toNat + (input.get! (3 + 2 * j)).toNat
  let d := 256 * (input.get! (2 + 2 * k)).toNat + (input.get! (3 + 2 * k)).toNat
  let m := input.extract (4 + 2 * k) input.size
  match (input.get! 0).toNat with
  | 0 => keccakStreamPieces Hash.sha3x224Init sizes m 28
  | 1 => keccakStreamPieces Hash.sha3x256Init sizes m 32
  | 2 => keccakStreamPieces Hash.sha3x384Init sizes m 48
  | 3 => keccakStreamPieces Hash.sha3x512Init sizes m 64
  | 4 => keccakStreamPieces Hash.shake128Init sizes m d
  | 5 => keccakStreamPieces Hash.shake256Init sizes m d
  | 6 => keccakStreamPieces Hash.keccak256Init sizes m 32
  | _ => ByteArray.empty

/-- Split a BLAKE2 input: the output length, key length, salt length and personalisation length
(one byte each), then the key, salt, personalisation and message. -/
def blake2Input (input : ByteArray) :
    Nat × ByteArray × ByteArray × ByteArray × ByteArray :=
  let nn := (input.get! 0).toNat
  let kk := (input.get! 1).toNat
  let sl := (input.get! 2).toNat
  let pl := (input.get! 3).toNat
  let a := 4 + kk
  let b := a + sl
  let c := b + pl
  (nn, input.extract 4 a, input.extract a b, input.extract b c, input.extract c input.size)

/-- BLAKE2b with key, salt, personalisation and output length, encoded as for `blake2Input`. -/
@[export hs_blake2b] def blake2b (input : ByteArray) : ByteArray :=
  let (nn, key, salt, personal, m) := blake2Input input
  Hash.blake2bWith key salt personal nn m
/-- BLAKE2s, with input as for `blake2b`. -/
@[export hs_blake2s] def blake2s (input : ByteArray) : ByteArray :=
  let (nn, key, salt, personal, m) := blake2Input input
  Hash.blake2sWith key salt personal nn m

/-- The EIP-152 BLAKE2b `F` precompile; the empty array on an invalid input. -/
@[export hs_blake2b_f] def blake2bF (input : ByteArray) : ByteArray :=
  match Hash.blake2bPrecompile input with
  | .ok out => out
  | .error _ => ByteArray.empty

/-- Add `m` to the BLAKE2 state `s` in pieces whose sizes cycle through `sizes`, then
finalize. -/
def blake2StreamPieces {α : Type} [Hash.BLAKE2.Fast.Word α] (s : Hash.BLAKE2.Fast.State α)
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

/-- The BLAKE2 streaming interface, for testing. The input is a variant byte (0 for BLAKE2b, 1
for BLAKE2s), a count `k`, `k` big-endian 16-bit piece sizes, and then the input of `blake2b`.
Returns the empty array on malformed input. -/
@[export hs_blake2_stream] def blake2Stream (input : ByteArray) : ByteArray :=
  let k := (input.get! 1).toNat
  if input.size < 6 + 2 * k then ByteArray.empty else
  let sizes := (List.range k).map fun j =>
    256 * (input.get! (2 + 2 * j)).toNat + (input.get! (3 + 2 * j)).toNat
  let (nn, key, salt, personal, m) := blake2Input (input.extract (2 + 2 * k) input.size)
  match (input.get! 0).toNat with
  | 0 => blake2StreamPieces (Hash.blake2bInit key salt personal nn) sizes m
  | 1 => blake2StreamPieces (Hash.blake2sInit key salt personal nn) sizes m
  | _ => ByteArray.empty

/-- Split a BLAKE3 input: the mode (0 `hash`, 1 `keyed_hash`, 2 `derive_key`), the output
length (four bytes, big-endian), the key or context length (two bytes, big-endian), the key
(32 bytes) or context string, then the message. -/
def blake3Input (input : ByteArray) : Nat × Nat × ByteArray × ByteArray :=
  let mode := (input.get! 0).toNat
  let d := (List.range 4).foldl (fun d i => 256 * d + (input.get! (1 + i)).toNat) 0
  let kl := 256 * (input.get! 5).toNat + (input.get! 6).toNat
  (mode, d, input.extract 7 (7 + kl), input.extract (7 + kl) input.size)

/-- BLAKE3 in any mode with any output length, encoded as for `blake3Input`; the empty array
for an unknown mode. -/
@[export hs_blake3] def blake3 (input : ByteArray) : ByteArray :=
  match blake3Input input with
  | (0, d, _, m) => Hash.blake3Xof m d
  | (1, d, key, m) => Hash.blake3Keyed key m d
  | (2, d, context, m) => Hash.blake3DeriveKey context m d
  | _ => ByteArray.empty

/-- Add `m` to the BLAKE3 state `s` in pieces whose sizes cycle through `sizes`, then finalize
with `d` bytes of output. -/
def blake3StreamPieces (s : Hash.BLAKE3.Fast.State) (sizes : List Nat) (m : ByteArray)
    (d : Nat) : ByteArray := Id.run do
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
  return s.finalize d

/-- The BLAKE3 streaming interface, for testing. The input is a count `k`, `k` big-endian 16-bit
piece sizes, and then the input of `blake3`. Returns the empty array on malformed input. -/
@[export hs_blake3_stream] def blake3Stream (input : ByteArray) : ByteArray :=
  let k := (input.get! 0).toNat
  if input.size < 8 + 2 * k then ByteArray.empty else
  let sizes := (List.range k).map fun j =>
    256 * (input.get! (1 + 2 * j)).toNat + (input.get! (2 + 2 * j)).toNat
  match blake3Input (input.extract (1 + 2 * k) input.size) with
  | (0, d, _, m) => blake3StreamPieces Hash.blake3Init sizes m d
  | (1, d, key, m) => blake3StreamPieces (Hash.blake3KeyedInit key) sizes m d
  | (2, d, context, m) => blake3StreamPieces (Hash.blake3DeriveKeyInit context) sizes m d
  | _ => ByteArray.empty

end HashFFI
