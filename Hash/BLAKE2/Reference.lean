/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Prelude.Bits

/-!
# BLAKE2: reference specification

A transcription of BLAKE2b and BLAKE2s as specified in RFC 7693, extended with the full parameter
block of the BLAKE2 specification (key, salt and personalisation). RFC 7693 works with `w`-bit
words read from bytes in little-endian order; the reference uses `BitVec w` for words and
`List UInt8` for byte strings.

The compression function `F` takes the number of rounds as an argument, as EIP-152 does for
Ethereum's BLAKE2b precompile; BLAKE2 itself uses 12 (BLAKE2b) or 10 (BLAKE2s) rounds.

## References

* [RFC 7693] M-J. Saarinen, J-P. Aumasson, *The BLAKE2 Cryptographic Hash and Message
  Authentication Code (MAC)*, RFC 7693, 2015. <https://www.rfc-editor.org/rfc/rfc7693>
* [BLAKE2] J-P. Aumasson, S. Neves, Z. Wilcox-O'Hearn, C. Winnerlein, *BLAKE2: simpler, smaller,
  fast as MD5*, ACNS 2013; and the specification at <https://www.blake2.net/blake2.pdf>.
* [EIP-152] T. Hess, M. Luongo, P. Dyraga, J. Hancock, *Add BLAKE2 compression function `F`
  precompile*, 2016. <https://eips.ethereum.org/EIPS/eip-152>
-/

@[expose] public section

namespace Hash.BLAKE2

/-- The parameters that distinguish BLAKE2b and BLAKE2s [RFC 7693, §2.1]. -/
structure Params where
  /-- The word size `w` in bits: 64 or 32. -/
  w : Nat
  /-- The number of rounds `r`: 12 or 10. -/
  rounds : Nat
  /-- The rotation constants `R1, R2, R3, R4`. -/
  R : Nat × Nat × Nat × Nat
  /-- The initialization vector `IV[0..7]` [RFC 7693, §2.6]. -/
  IV : List Nat
  /-- The block size `bb` in bytes: 128 or 64. -/
  blockBytes : Nat
  /-- The byte offset of the salt in the parameter block [BLAKE2, §2.5]. -/
  saltOffset : Nat
  /-- The length of the salt and of the personalisation string, in bytes [BLAKE2, §2.5]. -/
  saltBytes : Nat

/-- The message word permutations `SIGMA[0..9]` [RFC 7693, §2.7]. -/
def SIGMA : List (List Nat) :=
  [[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
   [14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
   [11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
   [ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
   [ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
   [ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
   [12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
   [13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
   [ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
   [10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]]

namespace Reference

variable (P : Params)

/-- The words of a byte string, each `w/8` bytes in little-endian order [RFC 7693, §2.4]. -/
def wordsLE (bs : List UInt8) : List (BitVec P.w) :=
  (chunks (P.w / 8) bs).map fun ws => BitVec.ofNat P.w (bitsToNatLE (bytesToBitsLSB ws))

/-- The bytes of a word, in little-endian order. -/
def bytesLE (x : BitVec P.w) : List UInt8 :=
  (List.range (P.w / 8)).map fun i => (x.toNat / 2 ^ (8 * i)).toUInt8

/-- The mixing function `G` [RFC 7693, §3.1]. -/
def G (v : List (BitVec P.w)) (a b c d : Nat) (x y : BitVec P.w) : List (BitVec P.w) :=
  let (R1, R2, R3, R4) := P.R
  let get (v : List (BitVec P.w)) i := v.getD i 0
  let v := v.set a (get v a + get v b + x)
  let v := v.set d ((get v d ^^^ get v a).rotateRight R1)
  let v := v.set c (get v c + get v d)
  let v := v.set b ((get v b ^^^ get v c).rotateRight R2)
  let v := v.set a (get v a + get v b + y)
  let v := v.set d ((get v d ^^^ get v a).rotateRight R3)
  let v := v.set c (get v c + get v d)
  v.set b ((get v b ^^^ get v c).rotateRight R4)

/-- One round of the compression function: `G` on the four columns, then on the four diagonals,
with message words selected by `SIGMA[i mod 10]` [RFC 7693, §3.2]. -/
def round (m : List (BitVec P.w)) (v : List (BitVec P.w)) (i : Nat) : List (BitVec P.w) :=
  let s := SIGMA.getD (i % 10) []
  let x (j : Nat) := m.getD (s.getD j 0) 0
  let v := G P v 0 4  8 12 (x 0) (x 1)
  let v := G P v 1 5  9 13 (x 2) (x 3)
  let v := G P v 2 6 10 14 (x 4) (x 5)
  let v := G P v 3 7 11 15 (x 6) (x 7)
  let v := G P v 0 5 10 15 (x 8) (x 9)
  let v := G P v 1 6 11 12 (x 10) (x 11)
  let v := G P v 2 7  8 13 (x 12) (x 13)
  G P v 3 4  9 14 (x 14) (x 15)

/-- The compression function `F` with `rounds` rounds [RFC 7693, §3.2]: initialise the work
vector from `h` and `IV`, mix in the offset counter `t` and the final-block flag `f`, apply the
rounds, and XOR the two halves into `h`. EIP-152 exposes this function for BLAKE2b with any
number of rounds. -/
def F (rounds : Nat) (h m : List (BitVec P.w)) (t : Nat) (f : Bool) : List (BitVec P.w) :=
  let iv := P.IV.map (BitVec.ofNat P.w)
  let v := h ++ iv
  let v := v.set 12 (v.getD 12 0 ^^^ BitVec.ofNat P.w t)
  let v := v.set 13 (v.getD 13 0 ^^^ BitVec.ofNat P.w (t / 2 ^ P.w))
  let v := if f then v.set 14 (~~~v.getD 14 0) else v
  let v := (List.range rounds).foldl (round P m) v
  (List.range 8).map fun i => h.getD i 0 ^^^ v.getD i 0 ^^^ v.getD (i + 8) 0

/-- The parameter block [BLAKE2, §2.5]: digest length, key length, fanout 1, depth 1, zeros for
the tree parameters, then the salt and the personalisation string, each zero-padded. RFC 7693
§3.3 uses this block with empty salt and personalisation. -/
def paramBlock (nn kk : Nat) (salt personal : List UInt8) : List UInt8 :=
  [nn.toUInt8, kk.toUInt8, 1, 1] ++ List.replicate (P.saltOffset - 4) 0 ++
    (salt ++ List.replicate (P.saltBytes - salt.length) 0).take P.saltBytes ++
    (personal ++ List.replicate (P.saltBytes - personal.length) 0).take P.saltBytes

/-- The data blocks `d[0..dd-1]` [RFC 7693, §3.3]: the key, if any, padded to a full block,
then the message zero-padded to whole blocks; one zero block for an empty message without key. -/
def blocks (key msg : List UInt8) : List (List UInt8) :=
  let bb := P.blockBytes
  let kk := key.length
  let ll := msg.length
  let keyBlock := if kk = 0 then [] else [key ++ List.replicate (bb - kk) 0]
  let msgBlocks := chunks bb (msg ++ List.replicate ((bb - ll % bb) % bb) 0)
  let d := keyBlock ++ msgBlocks
  if d = [] then [List.replicate bb 0] else d

/-- BLAKE2 with an `nn`-byte output, a key of at most `bb/2` bytes, and optional salt and
personalisation [RFC 7693, §3.3; BLAKE2, §2.5]. The data blocks are compressed in order; the
offset counter `t` counts the bytes processed, and the last block is compressed with the final
flag set. -/
def hash (key salt personal : List UInt8) (nn : Nat) (msg : List UInt8) : List UInt8 :=
  let bb := P.blockBytes
  let kk := key.length
  let ll := msg.length
  let h := List.zipWith (· ^^^ ·) (P.IV.map (BitVec.ofNat P.w))
    (wordsLE P (paramBlock P nn kk salt personal))
  let d := blocks P key msg
  let dd := d.length
  let h := (List.range (dd - 1)).foldl
    (fun h i => F P P.rounds h (wordsLE P (d.getD i [])) ((i + 1) * bb) false) h
  let t := if kk = 0 then ll else ll + bb
  let h := F P P.rounds h (wordsLE P (d.getD (dd - 1) [])) t true
  (h.flatMap (bytesLE P)).take nn

end Reference

/-! ### Members of the family -/

/-- BLAKE2b: 64-bit words, 12 rounds, 128-byte blocks [RFC 7693, §2.1]. Its IV is that of
SHA-512 [RFC 7693, §2.6]. -/
def blake2bParams : Params where
  w := 64
  rounds := 12
  R := (32, 24, 16, 63)
  IV := [0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
         0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]
  blockBytes := 128
  saltOffset := 32
  saltBytes := 16

/-- BLAKE2s: 32-bit words, 10 rounds, 64-byte blocks [RFC 7693, §2.1]. Its IV is that of
SHA-256 [RFC 7693, §2.6]. -/
def blake2sParams : Params where
  w := 32
  rounds := 10
  R := (16, 12, 8, 7)
  IV := [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
         0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
  blockBytes := 64
  saltOffset := 16
  saltBytes := 8

end Hash.BLAKE2
