/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import HashSpecs.Prelude.Bits

/-!
# SHA-2: reference specification

A transcription of the SHA-2 family of FIPS 180-4, written to be compared line by line with the
standard. Messages and digests are bit strings (`List Bool`, most significant bit first) and words
are `BitVec w`, matching the standard's data model [FIPS 180-4, §2.1, §3.1].

FIPS 180-4 describes SHA-224/256 (32-bit words, 64 rounds) and SHA-384/512/512-t (64-bit words,
80 rounds) separately, but with identical structure. We state that structure once, parameterised
by `Params`; the members of the family are instances in `HashSpecs.SHA2.Instances`.

This specification is meant to be read, not run on large inputs. The executable specification is
`HashSpecs.SHA2.Fast`, and the two are proved equal in `HashSpecs.SHA2.Equiv`.

## References

* [FIPS 180-4] NIST, *Secure Hash Standard (SHS)*, FIPS PUB 180-4, 2015.
  <https://doi.org/10.6028/NIST.FIPS.180-4>
-/

@[expose] public section

namespace HashSpecs.SHA2

/-- Rotation and shift amounts of one of the functions `Σ₀, Σ₁, σ₀, σ₁` [FIPS 180-4, §4.1.2,
§4.1.3]. `Σ` uses three rotations; `σ` uses two rotations and a final right shift. -/
structure Amounts where
  /-- The first rotation amount. -/
  r₁ : Nat
  /-- The second rotation amount. -/
  r₂ : Nat
  /-- The third rotation amount (for `Σ`) or right-shift amount (for `σ`). -/
  r₃ : Nat

/-- The parameters that distinguish the members of the SHA-2 family. -/
structure Params where
  /-- The word size `w` in bits: 32 or 64 [FIPS 180-4, §2.1]. -/
  w : Nat
  /-- The number of rounds per block: 64 or 80 [FIPS 180-4, §6.2.2, §6.4.2]. -/
  rounds : Nat
  /-- The round constants `K₀ … K_{rounds−1}` [FIPS 180-4, §4.2]. -/
  K : List Nat
  /-- The initial hash value `H⁽⁰⁾` (eight words) [FIPS 180-4, §5.3]. -/
  H0 : List Nat
  /-- The amounts for `Σ₀`. -/
  bigSigma0 : Amounts
  /-- The amounts for `Σ₁`. -/
  bigSigma1 : Amounts
  /-- The amounts for `σ₀`. -/
  smallSigma0 : Amounts
  /-- The amounts for `σ₁`. -/
  smallSigma1 : Amounts
  /-- The digest length in bits [FIPS 180-4, §6.3, §6.5, §6.6, §6.7]. -/
  digestBits : Nat

namespace Params

/-- The block size `m = 16 · w` in bits: 512 or 1024 [FIPS 180-4, §1, Figure 1]. -/
def blockBits (P : Params) : Nat := 16 * P.w

/-- The length of the message-length field appended by padding: 64 or 128 bits
[FIPS 180-4, §5.1.1, §5.1.2]. -/
def lengthBits (P : Params) : Nat := 2 * P.w

end Params

namespace Reference

variable {w : Nat}

/-! ### Functions [FIPS 180-4, §3.2, §4.1.2, §4.1.3] -/

/-- `ROTRⁿ(x)`, the circular right shift [FIPS 180-4, §3.2 (4)]. -/
def ROTR (n : Nat) (x : BitVec w) : BitVec w := x.rotateRight n

/-- `SHRⁿ(x)`, the right shift [FIPS 180-4, §3.2 (3)]. -/
def SHR (n : Nat) (x : BitVec w) : BitVec w := x >>> n

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)` [FIPS 180-4, (4.2), (4.8)]. -/
def Ch (x y z : BitVec w) : BitVec w := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)` [FIPS 180-4, (4.3), (4.9)]. -/
def Maj (x y z : BitVec w) : BitVec w := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ(x) = ROTR^{r₁}(x) ⊕ ROTR^{r₂}(x) ⊕ ROTR^{r₃}(x)`: the shape of `Σ₀` and `Σ₁`
[FIPS 180-4, (4.4), (4.5), (4.10), (4.11)]. -/
def bigSigma (a : Amounts) (x : BitVec w) : BitVec w :=
  ROTR a.r₁ x ^^^ ROTR a.r₂ x ^^^ ROTR a.r₃ x

/-- `σ(x) = ROTR^{r₁}(x) ⊕ ROTR^{r₂}(x) ⊕ SHR^{r₃}(x)`: the shape of `σ₀` and `σ₁`
[FIPS 180-4, (4.6), (4.7), (4.12), (4.13)]. -/
def smallSigma (a : Amounts) (x : BitVec w) : BitVec w :=
  ROTR a.r₁ x ^^^ ROTR a.r₂ x ^^^ SHR a.r₃ x

/-! ### Preprocessing [FIPS 180-4, §5] -/

/-- The number `k` of zero bits added by padding a message of `ℓ` bits: the smallest
non-negative `k` with `ℓ + 1 + k ≡ blockBits − lengthBits (mod blockBits)`
[FIPS 180-4, §5.1.1, §5.1.2]. -/
def padZeros (P : Params) (ℓ : Nat) : Nat :=
  (P.blockBits - (ℓ + 1 + P.lengthBits) % P.blockBits) % P.blockBits

/-- Padding [FIPS 180-4, §5.1.1, §5.1.2]: append the bit `1`, then `k` zero bits, then the
message length `ℓ` as a `lengthBits`-bit big-endian number. The standard requires
`ℓ < 2^lengthBits`; for longer messages only the low-order bits of `ℓ` are encoded. -/
def pad (P : Params) (M : List Bool) : List Bool :=
  M ++ [true] ++ List.replicate (padZeros P M.length) false ++ natToBitsBE P.lengthBits M.length

/-- Parsing [FIPS 180-4, §5.2]: split the padded message into blocks of `blockBits` bits, and
each block into sixteen `w`-bit words `M₀⁽ⁱ⁾ … M₁₅⁽ⁱ⁾`. -/
def parse (P : Params) (M : List Bool) : List (List (BitVec P.w)) :=
  (chunks P.blockBits M).map fun block =>
    (chunks P.w block).map fun word => BitVec.ofNat P.w (bitsToNatBE word)

/-! ### Hash computation [FIPS 180-4, §6.2.2, §6.4.2] -/

/-- Step 1: the message schedule `W₀ … W_{rounds−1}` of one block, where `Wₜ = Mₜ⁽ⁱ⁾` for
`t < 16` and `Wₜ = σ₁(W_{t−2}) + W_{t−7} + σ₀(W_{t−15}) + W_{t−16}` otherwise. -/
def schedule (P : Params) (M : List (BitVec P.w)) : List (BitVec P.w) :=
  (List.range P.rounds).foldl (init := []) fun W t =>
    W ++ [if t < 16 then M.getD t 0
          else smallSigma P.smallSigma1 (W.getD (t - 2) 0) + W.getD (t - 7) 0 +
            smallSigma P.smallSigma0 (W.getD (t - 15) 0) + W.getD (t - 16) 0]

/-- The eight working variables `a, b, …, h` [FIPS 180-4, §6.2.2 step 2]. The type is generic so
that the fast specification can reuse it with machine words. -/
structure Vars (β : Type) where
  /-- Working variable `a`. -/
  a : β
  /-- Working variable `b`. -/
  b : β
  /-- Working variable `c`. -/
  c : β
  /-- Working variable `d`. -/
  d : β
  /-- Working variable `e`. -/
  e : β
  /-- Working variable `f`. -/
  f : β
  /-- Working variable `g`. -/
  g : β
  /-- Working variable `h`. -/
  h : β

/-- Step 3: one round `t` of the compression function. -/
def round (P : Params) (W : List (BitVec P.w)) (v : Vars (BitVec P.w)) (t : Nat) :
    Vars (BitVec P.w) :=
  let T₁ := v.h + bigSigma P.bigSigma1 v.e + Ch v.e v.f v.g + BitVec.ofNat P.w (P.K.getD t 0) +
    W.getD t 0
  let T₂ := bigSigma P.bigSigma0 v.a + Maj v.a v.b v.c
  { h := v.g, g := v.f, f := v.e, e := v.d + T₁, d := v.c, c := v.b, b := v.a, a := T₁ + T₂ }

/-- Steps 1–4: process one message block `M`, updating the hash value `H`. -/
def compress (P : Params) (H : List (BitVec P.w)) (M : List (BitVec P.w)) : List (BitVec P.w) :=
  let W := schedule P M
  let v₀ : Vars (BitVec P.w) := ⟨H.getD 0 0, H.getD 1 0, H.getD 2 0, H.getD 3 0,
    H.getD 4 0, H.getD 5 0, H.getD 6 0, H.getD 7 0⟩
  let v := (List.range P.rounds).foldl (round P W) v₀
  [v.a + H.getD 0 0, v.b + H.getD 1 0, v.c + H.getD 2 0, v.d + H.getD 3 0,
    v.e + H.getD 4 0, v.f + H.getD 5 0, v.g + H.getD 6 0, v.h + H.getD 7 0]

/-- The initial hash value `H⁽⁰⁾` as words. -/
def initialHash (P : Params) : List (BitVec P.w) :=
  P.H0.map (BitVec.ofNat P.w)

/-- The hash function: pad and parse the message, compress each block in turn starting from
`H⁽⁰⁾`, and output the leftmost `digestBits` bits of the final hash value
[FIPS 180-4, §6.2.2, §6.3, §6.4.2, §6.5–6.7]. -/
def hash (P : Params) (M : List Bool) : List Bool :=
  let H := (parse P (pad P M)).foldl (compress P) (initialHash P)
  (H.flatMap fun h => natToBitsBE P.w h.toNat).take P.digestBits

end Reference

end HashSpecs.SHA2
