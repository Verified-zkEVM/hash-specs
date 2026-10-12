/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Keccak.Fast
public import Hash.Keccak.Stream

/-!
# SHA-3, SHAKE and Keccak-256: byte-level API

The functions of FIPS 202 and Ethereum's Keccak-256 on byte arrays, computed by the fast
specification. `Hash.Keccak.Equiv` proves each of them equal to the reference specification in
`Hash.Keccak.SHA3`.

For incremental hashing, start from `sha3x256Init` (or the other `…Init` states), absorb data with
`Hash.Keccak.Fast.State.update`, and finish with `Hash.Keccak.Fast.State.finalize`, or with
`Hash.Keccak.Fast.State.squeezeBytes` to choose a SHAKE output length.
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

/-! ### Incremental hashing -/

/-- The initial state of an incremental SHA3-224 computation. -/
def sha3x224Init : Keccak.Fast.State := .init 144 0x06 28

/-- The initial state of an incremental SHA3-256 computation. -/
def sha3x256Init : Keccak.Fast.State := .init 136 0x06 32

/-- The initial state of an incremental SHA3-384 computation. -/
def sha3x384Init : Keccak.Fast.State := .init 104 0x06 48

/-- The initial state of an incremental SHA3-512 computation. -/
def sha3x512Init : Keccak.Fast.State := .init 72 0x06 64

/-- The initial state of an incremental SHAKE128 computation (default output 32 bytes). -/
def shake128Init : Keccak.Fast.State := .init 168 0x1F 32

/-- The initial state of an incremental SHAKE256 computation (default output 64 bytes). -/
def shake256Init : Keccak.Fast.State := .init 136 0x1F 64

/-- The initial state of an incremental Keccak-256 computation. -/
def keccak256Init : Keccak.Fast.State := .init 136 0x01 32

end Hash
