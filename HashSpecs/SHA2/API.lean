/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import HashSpecs.SHA2.Fast
public import HashSpecs.SHA2.Instances

/-!
# SHA-2: byte-level API

The members of the SHA-2 family as functions on byte arrays, computed by the fast specification.
`HashSpecs.SHA2.Equiv` proves each of them equal to the reference specification.
-/

@[expose] public section

namespace HashSpecs

/-- SHA-224 [FIPS 180-4, §6.3]. -/
def sha224 (m : ByteArray) : ByteArray := SHA2.Fast.hashWith UInt32 SHA2.sha224 m

/-- SHA-256 [FIPS 180-4, §6.2]. -/
def sha256 (m : ByteArray) : ByteArray := SHA2.Fast.hashWith UInt32 SHA2.sha256 m

/-- SHA-384 [FIPS 180-4, §6.5]. -/
def sha384 (m : ByteArray) : ByteArray := SHA2.Fast.hashWith UInt64 SHA2.sha384 m

/-- SHA-512 [FIPS 180-4, §6.4]. -/
def sha512 (m : ByteArray) : ByteArray := SHA2.Fast.hashWith UInt64 SHA2.sha512 m

/-- SHA-512/224 [FIPS 180-4, §6.6]. -/
def sha512_224 (m : ByteArray) : ByteArray := SHA2.Fast.hashWith UInt64 SHA2.sha512_224 m

/-- SHA-512/256 [FIPS 180-4, §6.7]. -/
def sha512_256 (m : ByteArray) : ByteArray := SHA2.Fast.hashWith UInt64 SHA2.sha512_256 m

end HashSpecs
