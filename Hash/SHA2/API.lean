/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.SHA2.Fast
public import Hash.SHA2.Instances
public import Hash.SHA2.Stream

/-!
# SHA-2: byte-level API

The members of the SHA-2 family as functions on byte arrays, computed by the fast specification.
`Hash.SHA2.Equiv` proves each of them equal to the reference specification.

For incremental hashing, start from `sha256Init` (or the other `…Init` states), absorb data with
`Hash.SHA2.Fast.State.update`, and finish with `Hash.SHA2.Fast.State.finalize`.
-/

@[expose] public section

namespace Hash

/-- SHA-224 [FIPS 180-4, §6.3]. -/
def sha224 (m : ByteArray) : ByteArray := SHA2.Fast.hashWith UInt32 SHA2.sha224 m

/-- SHA-256 [FIPS 180-4, §6.2]. -/
def sha256 (m : ByteArray) : ByteArray := SHA2.Fast.hashWith UInt32 SHA2.sha256 m

/-- SHA-384 [FIPS 180-4, §6.5]. -/
def sha384 (m : ByteArray) : ByteArray := SHA2.Fast.hashWith UInt64 SHA2.sha384 m

/-- SHA-512 [FIPS 180-4, §6.4]. -/
def sha512 (m : ByteArray) : ByteArray := SHA2.Fast.hashWith UInt64 SHA2.sha512 m

/-- SHA-512/224 [FIPS 180-4, §6.6]. -/
def sha512t224 (m : ByteArray) : ByteArray := SHA2.Fast.hashWith UInt64 SHA2.sha512t224 m

/-- SHA-512/256 [FIPS 180-4, §6.7]. -/
def sha512t256 (m : ByteArray) : ByteArray := SHA2.Fast.hashWith UInt64 SHA2.sha512t256 m

/-! ### Incremental hashing -/

/-- The initial state of an incremental SHA-224 computation. -/
def sha224Init : SHA2.Fast.State UInt32 := .init UInt32 SHA2.sha224

/-- The initial state of an incremental SHA-256 computation. -/
def sha256Init : SHA2.Fast.State UInt32 := .init UInt32 SHA2.sha256

/-- The initial state of an incremental SHA-384 computation. -/
def sha384Init : SHA2.Fast.State UInt64 := .init UInt64 SHA2.sha384

/-- The initial state of an incremental SHA-512 computation. -/
def sha512Init : SHA2.Fast.State UInt64 := .init UInt64 SHA2.sha512

/-- The initial state of an incremental SHA-512/224 computation. -/
def sha512t224Init : SHA2.Fast.State UInt64 := .init UInt64 SHA2.sha512t224

/-- The initial state of an incremental SHA-512/256 computation. -/
def sha512t256Init : SHA2.Fast.State UInt64 := .init UInt64 SHA2.sha512t256

end Hash
