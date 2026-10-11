/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.SHA2.Constants
public import Hash.SHA2.Reference

/-!
# SHA-2: the members of the family

The parameters of SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256
[FIPS 180-4, §4.1.2, §4.1.3, §4.2, §5.3, §6].

## References

* [FIPS 180-4] NIST, *Secure Hash Standard (SHS)*, FIPS PUB 180-4, 2015.
  <https://doi.org/10.6028/NIST.FIPS.180-4>
-/

@[expose] public section

namespace Hash.SHA2

/-- The rotation amounts shared by SHA-224 and SHA-256 [FIPS 180-4, (4.4)–(4.7)]. -/
def params32 (H0 : List Nat) (digestBits : Nat) : Params where
  w := 32
  rounds := 64
  K := K256
  H0 := H0
  bigSigma0 := ⟨2, 13, 22⟩
  bigSigma1 := ⟨6, 11, 25⟩
  smallSigma0 := ⟨7, 18, 3⟩
  smallSigma1 := ⟨17, 19, 10⟩
  digestBits := digestBits

/-- The rotation amounts shared by SHA-384, SHA-512 and SHA-512/t [FIPS 180-4, (4.10)–(4.13)]. -/
def params64 (H0 : List Nat) (digestBits : Nat) : Params where
  w := 64
  rounds := 80
  K := K512
  H0 := H0
  bigSigma0 := ⟨28, 34, 39⟩
  bigSigma1 := ⟨14, 18, 41⟩
  smallSigma0 := ⟨1, 8, 7⟩
  smallSigma1 := ⟨19, 61, 6⟩
  digestBits := digestBits

/-- SHA-224 [FIPS 180-4, §6.3]. -/
def sha224 : Params := params32 H0_224 224

/-- SHA-256 [FIPS 180-4, §6.2]. -/
def sha256 : Params := params32 H0_256 256

/-- SHA-384 [FIPS 180-4, §6.5]. -/
def sha384 : Params := params64 H0_384 384

/-- SHA-512 [FIPS 180-4, §6.4]. -/
def sha512 : Params := params64 H0_512 512

/-- SHA-512/224 [FIPS 180-4, §6.6]. -/
def sha512_224 : Params := params64 H0_512_224 224

/-- SHA-512/256 [FIPS 180-4, §6.7]. -/
def sha512_256 : Params := params64 H0_512_256 256

/-! ### The SHA-512/t initial hash values [FIPS 180-4, §5.3.6] -/

/-- The SHA-512/t IV generation function [FIPS 180-4, §5.3.6]: SHA-512 with initial value
`H⁽⁰⁾″ = H⁽⁰⁾ ⊕ a5a5a5a5a5a5a5a5` (the SHA-512 initial value XORed word-wise), applied to the
ASCII string `"SHA-512/t"`. The 512-bit result is the initial hash value of SHA-512/t. -/
def sha512tIV (name : List UInt8) : List Nat :=
  let P := params64 (H0_512.map (· ^^^ 0xa5a5a5a5a5a5a5a5)) 512
  (chunks 64 (Reference.hash P (bytesToBitsMSB name))).map bitsToNatBE

end Hash.SHA2
