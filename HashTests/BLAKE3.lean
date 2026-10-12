/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

import Hash.BLAKE3.API

/-!
# BLAKE3 known-answer tests (kernel-checked)

A small representative subset of the BLAKE3 team's `test_vectors.json`, checked by the kernel
with `decide +kernel`: the 32-byte outputs of the three modes on the empty input, and of `hash`
on one byte and on 65 bytes (two blocks of one chunk). Inputs of several chunks take minutes in
the kernel; they are covered by the full suite in `hash-kat`.
-/

namespace HashTests.BLAKE3

open Hash

/-- The test input of length `n`: the bytes `0, 1, …, 250` repeated. -/
def input (n : Nat) : ByteArray := ⟨((List.range n).map fun i => (i % 251).toUInt8).toArray⟩

/-- The bytes of a string literal known to be ASCII. -/
def ascii (s : String) : ByteArray := ⟨(s.toList.map fun c => c.toNat.toUInt8).toArray⟩

set_option maxRecDepth 100000

example : (blake3 (input 0)).toHex =
    "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262" := by
  decide +kernel

example : (blake3 (input 1)).toHex =
    "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213" := by
  decide +kernel

example : (blake3Keyed (ascii "whats the Elvish word for friend") (input 0) 32).toHex =
    "92b2b75604ed3c761f9d6f62392c8a9227ad0ea3f09573e783f1498a4ed60d26" := by
  decide +kernel

example : (blake3DeriveKey (ascii "BLAKE3 2019-12-27 16:29:52 test vectors context")
      (input 0) 32).toHex =
    "2cc39783c223154fea8dfb7c1b1660f2ac2dcbd1c1de8277b0b0dd39b7e50d7d" := by
  decide +kernel

example : (blake3 (input 65)).toHex =
    "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee" := by
  decide +kernel

end HashTests.BLAKE3
