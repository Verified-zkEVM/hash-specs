/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Keccak.Fast

/-!
# SHA-3, SHAKE and Keccak-256: byte-level API

The functions of FIPS 202 and Ethereum's Keccak-256 on byte arrays, computed by the fast
specification. `Hash.Keccak.Equiv` proves each of them equal to the reference specification in
`Hash.Keccak.SHA3`.
-/

@[expose] public section

namespace Hash

/-- SHA3-224 [FIPS 202, §6.1]. -/
def sha3x224 (m : ByteArray) : ByteArray := Keccak.Fast.sponge 144 0x06 m 28

/-- SHA3-256 [FIPS 202, §6.1]. -/
def sha3x256 (m : ByteArray) : ByteArray := Keccak.Fast.sponge 136 0x06 m 32

/-- SHA3-384 [FIPS 202, §6.1]. -/
def sha3x384 (m : ByteArray) : ByteArray := Keccak.Fast.sponge 104 0x06 m 48

/-- SHA3-512 [FIPS 202, §6.1]. -/
def sha3x512 (m : ByteArray) : ByteArray := Keccak.Fast.sponge 72 0x06 m 64

/-- SHAKE128 with an output of `d` bytes [FIPS 202, §6.2]. -/
def shake128 (m : ByteArray) (d : Nat) : ByteArray := Keccak.Fast.sponge 168 0x1F m d

/-- SHAKE256 with an output of `d` bytes [FIPS 202, §6.2]. -/
def shake256 (m : ByteArray) (d : Nat) : ByteArray := Keccak.Fast.sponge 136 0x1F m d

/-- Ethereum's Keccak-256: the original Keccak padding, without SHA-3's domain separation. -/
def keccak256 (m : ByteArray) : ByteArray := Keccak.Fast.sponge 136 0x01 m 32

end Hash
