/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Construction.Sponge
public import Hash.Keccak.KeccakP

/-!
# SHA-3, SHAKE and Keccak-256: reference specification

The Keccak sponge functions KECCAK[c] and the members of FIPS 202 built on them: the hash
functions SHA3-224, SHA3-256, SHA3-384 and SHA3-512, and the extendable-output functions
SHAKE128 and SHAKE256. They differ in the capacity `c` and in the domain-separation bits appended
to the message.

Ethereum's Keccak-256 is the original Keccak submission's 256-bit hash: KECCAK[512] with no
domain-separation bits. It predates the final SHA-3 standard, so it differs from SHA3-256.

Messages and outputs are bit strings. Byte strings are converted with the convention of
FIPS 202, Appendix B.1: each byte is read least significant bit first (`Hash.bytesToBitsLSB`).

## References

* [FIPS 202] NIST, *SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions*,
  FIPS PUB 202, 2015. <https://doi.org/10.6028/NIST.FIPS.202>
* G. Wood, *Ethereum: A Secure Decentralised Generalised Transaction Ledger*, Appendix on
  `KEC`. <https://ethereum.github.io/yellowpaper/paper.pdf>
-/

@[expose] public section

namespace Hash.Keccak.Reference

/-- KECCAK[c] = SPONGE[Keccak-p[1600, 24], pad10*1, 1600 − c] [FIPS 202, §5.2]. -/
def keccak (c : Nat) (N : List Bool) (d : Nat) : List Bool :=
  Sponge.sponge (keccakP 6 24) Sponge.pad101 1600 (1600 - c) N d

/-- SHA3-224(M) = KECCAK[448](M ‖ 01, 224) [FIPS 202, §6.1]. -/
def sha3x224 (M : List Bool) : List Bool := keccak 448 (M ++ [false, true]) 224

/-- SHA3-256(M) = KECCAK[512](M ‖ 01, 256) [FIPS 202, §6.1]. -/
def sha3x256 (M : List Bool) : List Bool := keccak 512 (M ++ [false, true]) 256

/-- SHA3-384(M) = KECCAK[768](M ‖ 01, 384) [FIPS 202, §6.1]. -/
def sha3x384 (M : List Bool) : List Bool := keccak 768 (M ++ [false, true]) 384

/-- SHA3-512(M) = KECCAK[1024](M ‖ 01, 512) [FIPS 202, §6.1]. -/
def sha3x512 (M : List Bool) : List Bool := keccak 1024 (M ++ [false, true]) 512

/-- SHAKE128(M, d) = KECCAK[256](M ‖ 1111, d) [FIPS 202, §6.2]. -/
def shake128 (M : List Bool) (d : Nat) : List Bool :=
  keccak 256 (M ++ [true, true, true, true]) d

/-- SHAKE256(M, d) = KECCAK[512](M ‖ 1111, d) [FIPS 202, §6.2]. -/
def shake256 (M : List Bool) (d : Nat) : List Bool :=
  keccak 512 (M ++ [true, true, true, true]) d

/-- Ethereum's Keccak-256: KECCAK[512](M, 256), without domain-separation bits. -/
def keccak256 (M : List Bool) : List Bool := keccak 512 M 256

end Hash.Keccak.Reference
