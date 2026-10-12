/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.BLAKE3.Stream

/-!
# BLAKE3: byte-level API

The three modes of BLAKE3 on byte arrays, with any output length, and their streaming initial
states, computed by the fast specification.
-/

@[expose] public section

namespace Hash

open BLAKE3 BLAKE3.Fast

/-- BLAKE3 with `d` bytes of output [BLAKE3, §2.3, §2.6]. -/
def blake3Xof (m : ByteArray) (d : Nat) : ByteArray := hashWith ivWords 0 m d

/-- BLAKE3 with its default 32-byte output. -/
def blake3 (m : ByteArray) : ByteArray := blake3Xof m 32

/-- BLAKE3 `keyed_hash` with a 32-byte key and `d` bytes of output [BLAKE3, §2.3]. -/
def blake3Keyed (key m : ByteArray) (d : Nat) : ByteArray :=
  hashWith (keyWords key) KEYED_HASH m d

/-- The context key of `derive_key`: the context string hashed with `DERIVE_KEY_CONTEXT`. -/
def blake3ContextKey (context : ByteArray) : Array UInt32 :=
  keyWords (hashWith ivWords DERIVE_KEY_CONTEXT context 32)

/-- BLAKE3 `derive_key` with `d` bytes of output [BLAKE3, §2.3, §6.2]. -/
def blake3DeriveKey (context material : ByteArray) (d : Nat) : ByteArray :=
  hashWith (blake3ContextKey context) DERIVE_KEY_MATERIAL material d

/-- The initial streaming state of `blake3Xof`. -/
def blake3Init : State := .init ivWords 0

/-- The initial streaming state of `blake3Keyed key`. -/
def blake3KeyedInit (key : ByteArray) : State := .init (keyWords key) KEYED_HASH

/-- The initial streaming state of `blake3DeriveKey context`. -/
def blake3DeriveKeyInit (context : ByteArray) : State :=
  .init (blake3ContextKey context) DERIVE_KEY_MATERIAL

end Hash
