import Hash
namespace EA
abbrev Word := BitVec 64
/-- The 24 Keccak round constants. -/
def keccakRC : List (BitVec 64) :=
  [0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
   0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
   0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
   0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
   0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
   0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
   0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
   0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rho rotation offsets, indexed `rhoOff x y` for lane (x, y). -/
def rhoOff (x y : Nat) : Nat :=
  ([[0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14]].getD (x % 5) []).getD (y % 5) 0

/-- One Keccak-f round on the 5×5 lane state (lane (x, y) at index
    `x + 5*y`).  The result is MATERIALIZED as a list: composing rounds
    over a functional state would re-evaluate shared lanes exponentially. -/
def keccakRound (rc : BitVec 64) (st : List (BitVec 64)) : List (BitVec 64) :=
  let A : Nat → Nat → BitVec 64 := fun x y => st.getD (x % 5 + 5 * (y % 5)) 0
  let C : Nat → BitVec 64 := fun x => A x 0 ^^^ A x 1 ^^^ A x 2 ^^^ A x 3 ^^^ A x 4
  let D : Nat → BitVec 64 := fun x => C (x + 4) ^^^ (C (x + 1)).rotateLeft 1
  -- theta, then rho+pi: B[X + 5Y] sources lane (X + 3Y, X)
  let B : Nat → Nat → BitVec 64 := fun X Y =>
    let xs := (X + 3 * Y) % 5
    let ys := X % 5
    (A xs ys ^^^ D xs).rotateLeft (rhoOff xs ys)
  let chi : Nat → BitVec 64 := fun j =>
    let X := j % 5
    let Y := j / 5
    B X Y ^^^ ((~~~(B (X + 1) Y)) &&& B (X + 2) Y)
  List.ofFn (n := 25) (fun j => if j.val = 0 then chi 0 ^^^ rc else chi j.val)

/-- Keccak-f[1600]: 24 rounds over the 25-lane state. -/
def keccakF (st : List (BitVec 64)) : List (BitVec 64) :=
  keccakRC.foldl (fun s rc => keccakRound rc s) st


/-- The 64 SHA-256 round constants. -/
def sha256K : List (BitVec 32) :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
   0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
   0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
   0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
   0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
   0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
   0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
   0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
   0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Message schedule: extend the 16 block words to 64. -/
def sha256W (w : List (BitVec 32)) : List (BitVec 32) :=
  (List.range 64).foldl (fun acc t =>
    if t < 16 then acc ++ [w.getD t 0]
    else
      let s0 := (acc.getD (t - 15) 0).rotateRight 7
        ^^^ (acc.getD (t - 15) 0).rotateRight 18 ^^^ (acc.getD (t - 15) 0 >>> 3)
      let s1 := (acc.getD (t - 2) 0).rotateRight 17
        ^^^ (acc.getD (t - 2) 0).rotateRight 19 ^^^ (acc.getD (t - 2) 0 >>> 10)
      acc ++ [acc.getD (t - 16) 0 + s0 + acc.getD (t - 7) 0 + s1]) []

/-- One SHA-256 compression: 8-word state, 16-word block, new 8-word
    state (Davies–Meyer feed-forward included). -/
def sha256Compress (hs w : List (BitVec 32)) : List (BitVec 32) :=
  let W := sha256W w
  let fin := (List.range 64).foldl (fun st t =>
    let a := st.getD 0 0
    let b := st.getD 1 0
    let c := st.getD 2 0
    let d := st.getD 3 0
    let e := st.getD 4 0
    let f := st.getD 5 0
    let g := st.getD 6 0
    let h := st.getD 7 0
    let S1 := e.rotateRight 6 ^^^ e.rotateRight 11 ^^^ e.rotateRight 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let T1 := h + S1 + ch + sha256K.getD t 0 + W.getD t 0
    let S0 := a.rotateRight 2 ^^^ a.rotateRight 13 ^^^ a.rotateRight 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let T2 := S0 + maj
    [T1 + T2, a, b, c, d + T1, e, f, g]) (hs.take 8)
  List.zipWith (· + ·) (hs.take 8) fin


/-- The BLAKE2b message-schedule permutations (SIGMA), rows 0–9. -/
def blake2Sigma : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
   [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
   [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
   [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
   [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
   [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
   [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
   [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
   [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- The BLAKE2b G mixing function on working-vector indices
    `a b c d` with message words `x y`. -/
def blakeG (v : List (BitVec 64)) (a b c d : Nat) (x y : BitVec 64) :
    List (BitVec 64) :=
  let va := v.getD a 0 + v.getD b 0 + x
  let vd := (v.getD d 0 ^^^ va).rotateRight 32
  let vc := v.getD c 0 + vd
  let vb := (v.getD b 0 ^^^ vc).rotateRight 24
  let va' := va + vb + y
  let vd' := (vd ^^^ va').rotateRight 16
  let vc' := vc + vd'
  let vb' := (vb ^^^ vc').rotateRight 63
  (((v.set a va').set b vb').set c vc').set d vd'

/-- One BLAKE2b round (RFC 7693 §3.2): four column and four diagonal G
    mixes of the 16-word working vector `v` with message words `m`,
    using SIGMA row `idx % 10`.  Exactly the ZisK `Blake2bRound`
    accelerator body (`precompiles/helpers/src/blake2/blake2b/round.rs`);
    the software F loop iterates it `rounds` times. -/
def blake2bRound (idx : Nat) (v m : List (BitVec 64)) : List (BitVec 64) :=
  let s := blake2Sigma.getD (idx % 10) []
  let mi : Nat → BitVec 64 := fun i => m.getD (s.getD i 0) 0
  let v1 := blakeG v 0 4 8 12 (mi 0) (mi 1)
  let v2 := blakeG v1 1 5 9 13 (mi 2) (mi 3)
  let v3 := blakeG v2 2 6 10 14 (mi 4) (mi 5)
  let v4 := blakeG v3 3 7 11 15 (mi 6) (mi 7)
  let v5 := blakeG v4 0 5 10 15 (mi 8) (mi 9)
  let v6 := blakeG v5 1 6 11 12 (mi 10) (mi 11)
  let v7 := blakeG v6 2 7 8 13 (mi 12) (mi 13)
  blakeG v7 3 4 9 14 (mi 14) (mi 15)

abbrev Byte := BitVec 8
abbrev Bytes := List Byte
def bytesBEtoNat (bs : Bytes) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0
/-- Interpret bytes as a little-endian natural number (first byte least
    significant). -/
def bytesLEtoNat : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesLEtoNat bs

/-- The low `width` bytes of `x`, little-endian (first byte least
    significant). -/
def natToBytesLE (width x : Nat) : Bytes :=
  (List.range width).map (fun i => BitVec.ofNat 8 (x >>> (8 * i)))

/-- The low `width` bytes of `x`, big-endian (first byte most
    significant). Fixed-width companion to the minimal
    `EvmAsm.EL.RLP.Nat.toBytesBE`. -/
def natToBytesBE (width x : Nat) : Bytes :=
  (List.range width).reverse.map (fun i => BitVec.ofNat 8 (x >>> (8 * i)))

/-- Split a byte list into chunks of `n` bytes (last chunk full only when
    the length is a multiple of `n`, which is always the case for padded
    hash inputs). Fuel = input length guarantees termination. -/
def chunkBytesAux : Nat → Nat → Bytes → List Bytes
  | 0, _, _ => []
  | _, _, [] => []
  | fuel + 1, n, bs => bs.take n :: chunkBytesAux fuel n (bs.drop n)

/-- Split `bs` into `n`-byte chunks. -/
def chunkBytes (n : Nat) (bs : Bytes) : List Bytes :=
  chunkBytesAux (bs.length + 1) n bs

/-! ## Keccak-256 (sponge over `keccakF`) -/

/-- Keccak-256 rate in bytes (1088-bit rate, 512-bit capacity). -/
def keccakRateBytes : Nat := 136

/-- `pad10*1` with the Keccak domain byte `0x01`: append `0x01`, then
    zeros, then set the top bit of the final rate byte (`0x80`). When only
    one pad byte fits, the two collapse to `0x81`. -/
def keccakPad (msg : Bytes) : Bytes :=
  let padLen := keccakRateBytes - (msg.length % keccakRateBytes)
  let pad :=
    if padLen = 1 then [(0x81 : Byte)]
    else (0x01 : Byte) :: List.replicate (padLen - 2) (0 : Byte) ++ [(0x80 : Byte)]
  msg ++ pad

/-- XOR a 136-byte rate block (as 17 little-endian u64 lanes) into the
    25-lane state. -/
def keccakAbsorbBlock (st : List (BitVec 64)) (block : Bytes) : List (BitVec 64) :=
  let lanes : List (BitVec 64) :=
    (List.range 17).map (fun i =>
      BitVec.ofNat 64 (bytesLEtoNat ((block.drop (8 * i)).take 8)))
  let laneVec := lanes ++ List.replicate (25 - lanes.length) (0 : BitVec 64)
  List.zipWith (· ^^^ ·) st laneVec

/-- Absorb all rate blocks, permuting after each. -/
def keccakAbsorb : List (BitVec 64) → List Bytes → List (BitVec 64)
  | st, [] => st
  | st, block :: rest => keccakAbsorb (keccakF (keccakAbsorbBlock st block)) rest

/-- `keccak256(msg)` — the 32-byte digest (first four state lanes, each
    little-endian). Mirrors `ethereum.crypto.hash.keccak256`. -/
def keccak256 (msg : Bytes) : Bytes :=
  let st0 : List (BitVec 64) := List.replicate 25 (0 : BitVec 64)
  let st := keccakAbsorb st0 (chunkBytes keccakRateBytes (keccakPad msg))
  (st.take 4).flatMap (fun lane => natToBytesLE 8 lane.toNat)

/-! ## SHA-256 (Merkle–Damgård over `sha256Compress`) -/

/-- The SHA-256 initial hash value (eight 32-bit words). -/
def sha256IV : List (BitVec 32) :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- SHA-256 padding: append `0x80`, zero-pad, then the 64-bit big-endian
    bit length, filling to a multiple of 64 bytes. -/
def sha256Pad (msg : Bytes) : Bytes :=
  let l := msg.length
  let zeros := (64 - ((l + 9) % 64)) % 64
  msg ++ [(0x80 : Byte)] ++ List.replicate zeros (0 : Byte)
      ++ natToBytesBE 8 (l * 8)

/-- Interpret a 64-byte block as sixteen 32-bit big-endian words. -/
def sha256BlockWords (block : Bytes) : List (BitVec 32) :=
  (List.range 16).map (fun i =>
    BitVec.ofNat 32 (bytesBEtoNat ((block.drop (4 * i)).take 4)))

/-- Fold the compression function over all 64-byte blocks. -/
def sha256Compress' : List (BitVec 32) → List Bytes → List (BitVec 32)
  | hs, [] => hs
  | hs, block :: rest =>
      sha256Compress' (sha256Compress hs (sha256BlockWords block)) rest

/-- `sha256(msg)` — the 32-byte digest. Mirrors `hashlib.sha256`. -/
def sha256 (msg : Bytes) : Bytes :=
  let hs := sha256Compress' sha256IV (chunkBytes 64 (sha256Pad msg))
  hs.flatMap (fun w => natToBytesBE 4 w.toNat)

/-- `sha256(a ‖ b)` — the SSZ pair hash used in merkleization. -/
def sha256Pair (a b : Bytes) : Bytes := sha256 (a ++ b)
/-! ## RIPEMD-160 primitive -/

namespace Ripemd160

def M32 : Nat := 2^32

def rotl (s : Nat) (x : Nat) : Nat :=
  ((x <<< s) ||| (x >>> (32 - s))) % M32

/-- Selection functions f₁…f₅ (per 16-step block `j/16`). -/
def f (j : Nat) (x y z : Nat) : Nat :=
  if j < 16 then x ^^^ y ^^^ z
  else if j < 32 then (x &&& y) ||| ((M32 - 1 - x) &&& z)
  else if j < 48 then (x ||| (M32 - 1 - y)) ^^^ z
  else if j < 64 then (x &&& z) ||| (y &&& (M32 - 1 - z))
  else x ^^^ (y ||| (M32 - 1 - z))

def K : List Nat := [0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]
def K' : List Nat := [0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

def r : List Nat :=
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
   7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8,
   3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12,
   1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2,
   4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13]

def r' : List Nat :=
  [5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12,
   6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2,
   15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13,
   8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14,
   12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11]

def s : List Nat :=
  [11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8,
   7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12,
   11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5,
   11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12,
   9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6]

def s' : List Nat :=
  [8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6,
   9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11,
   9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5,
   15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8,
   8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11]

/-- One 512-bit block: 80 steps of the left and right lines, then the
    chaining combination. -/
def compressBlock (h : List Nat) (X : List Nat) : List Nat := Id.run do
  let mut a := h.getD 0 0
  let mut b := h.getD 1 0
  let mut c := h.getD 2 0
  let mut d := h.getD 3 0
  let mut e := h.getD 4 0
  let mut a' := a
  let mut b' := b
  let mut c' := c
  let mut d' := d
  let mut e' := e
  for j in [0:80] do
    -- left line
    let t := rotl (s.getD j 0)
      ((a + f j b c d + X.getD (r.getD j 0) 0 + K.getD (j / 16) 0) % M32)
    let t := (t + e) % M32
    a := e; e := d; d := rotl 10 c; c := b; b := t
    -- right line (f with reversed block order)
    let t' := rotl (s'.getD j 0)
      ((a' + f (79 - j) b' c' d' + X.getD (r'.getD j 0) 0 + K'.getD (j / 16) 0) % M32)
    let t' := (t' + e') % M32
    a' := e'; e' := d'; d' := rotl 10 c'; c' := b'; b' := t'
  let h0 := h.getD 0 0
  let h1 := h.getD 1 0
  let h2 := h.getD 2 0
  let h3 := h.getD 3 0
  let h4 := h.getD 4 0
  pure [(h1 + c + d') % M32, (h2 + d + e') % M32, (h3 + e + a') % M32,
        (h4 + a + b') % M32, (h0 + b + c') % M32]

def leWord (bs : Bytes) : Nat :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0

def wordLE (n : Nat) : Bytes :=
  (List.range 4).map (fun i => BitVec.ofNat 8 (n >>> (8 * i)))

def chunksAux (n : Nat) : Nat → Bytes → List Bytes
  | 0, _ => []
  | _, [] => []
  | fuel + 1, bs => bs.take n :: chunksAux n fuel (bs.drop n)

/-- Split into `n`-byte chunks.  Structurally fueled by `bs.length`,
    which bounds the chunk count whenever `n ≥ 1` (each chunk consumes
    at least one byte). -/
def chunks (n : Nat) (bs : Bytes) : List Bytes :=
  if n == 0 then [] else chunksAux n bs.length bs

/-- RIPEMD-160 of a byte string (MD-style padding, little-endian
    length). -/
def hash (data : Bytes) : Bytes :=
  let bitLen := data.length * 8
  let padLen := (119 - data.length % 64) % 64 + 1  -- to ≡ 56 mod 64
  let padded := data ++ [(0x80 : BitVec 8)]
    ++ List.replicate (padLen - 1) (0x00 : BitVec 8)
    ++ (List.range 8).map (fun i => BitVec.ofNat 8 (bitLen >>> (8 * i)))
  let blocks := chunks 64 padded
  let h0 := [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]
  let hFinal := blocks.foldl (fun h block =>
    compressBlock h ((chunks 4 block).map leWord)) h0
  hFinal.flatMap wordLE

end Ripemd160
/-! ## BLAKE2b compression (`ethereum/crypto/blake2.py`, class `Blake2b`) -/

namespace Blake2b

def M64 : Nat := 2^64

def IV : List Nat :=
  [0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B,
   0xA54FF53A5F1D36F1, 0x510E527FADE682D1, 0x9B05688C2B3E6C1F,
   0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]

def sigma : List (List Nat) :=
  [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
   [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
   [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],
   [7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
   [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],
   [2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
   [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],
   [13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
   [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],
   [10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0]]

def mixTable : List (Nat × Nat × Nat × Nat) :=
  [(0,4,8,12), (1,5,9,13), (2,6,10,14), (3,7,11,15),
   (0,5,10,15), (1,6,11,12), (2,7,8,13), (3,4,9,14)]

def rotr (n : Nat) (x : Nat) : Nat :=
  ((x >>> n) ||| (x <<< (64 - n))) % M64

/-- The `G` mixing function (rotations 32/24/16/63). -/
def G (v : List Nat) (a b c d : Nat) (x y : Nat) : List Nat := Id.run do
  let mut v := v
  v := v.set a ((v.getD a 0 + v.getD b 0 + x) % M64)
  v := v.set d (rotr 32 (v.getD d 0 ^^^ v.getD a 0))
  v := v.set c ((v.getD c 0 + v.getD d 0) % M64)
  v := v.set b (rotr 24 (v.getD b 0 ^^^ v.getD c 0))
  v := v.set a ((v.getD a 0 + v.getD b 0 + y) % M64)
  v := v.set d (rotr 16 (v.getD d 0 ^^^ v.getD a 0))
  v := v.set c ((v.getD c 0 + v.getD d 0) % M64)
  v := v.set b (rotr 63 (v.getD b 0 ^^^ v.getD c 0))
  pure v

/-- `compress(num_rounds, h, m, t_0, t_1, f)` — 'F Compression' of
    RFC 7693 §3.2. -/
def compress (num_rounds : Nat) (h m : List Nat) (t0 t1 : Nat) (f : Bool) :
    Bytes := Id.run do
  let mut v := h ++ IV
  v := v.set 12 ((v.getD 12 0) ^^^ t0)
  v := v.set 13 ((v.getD 13 0) ^^^ t1)
  if f then
    v := v.set 14 ((v.getD 14 0) ^^^ (M64 - 1))
  for rnd in [0:num_rounds] do
    let sch := sigma.getD (rnd % 10) []
    let mut i := 0
    for (a, b, c, d) in mixTable do
      v := G v a b c d (m.getD (sch.getD (2*i) 0) 0) (m.getD (sch.getD (2*i+1) 0) 0)
      i := i + 1
  let out := (List.range 8).map (fun i => (h.getD i 0) ^^^ (v.getD i 0) ^^^ (v.getD (i+8) 0))
  pure (out.flatMap (fun w => (List.range 8).map (fun i => BitVec.ofNat 8 (w >>> (8*i)))))

/-- `spit_le_to_uint(data, start, num_words)`: 64-bit LE words. -/
def leWords (data : Bytes) (start count : Nat) : List Nat :=
  (List.range count).map (fun i =>
    ((data.drop (start + 8*i)).take 8).foldr (fun b acc => acc * 256 + b.toNat) 0)

end Blake2b
end EA

open EA

def toBA (l : List (BitVec 8)) : ByteArray := ⟨(l.map (fun b => b.toNat.toUInt8)).toArray⟩
def ofBA (b : ByteArray) : List (BitVec 8) := b.data.toList.map (fun u => BitVec.ofNat 8 u.toNat)

-- deterministic PRNG
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64
def rbytes (seed n : Nat) : List (BitVec 8) := Id.run do
  let mut s := seed; let mut out := #[]
  for _ in [0:n] do
    s := lcg s; out := out.push (BitVec.ofNat 8 (s >>> 33))
  return out.toList
def rwords (seed n w : Nat) : List Nat := Id.run do
  let mut s := seed; let mut out := #[]
  for _ in [0:n] do
    s := lcg s; let a := s; s := lcg s
    out := out.push (((a >>> 32) * 2^32 + (s >>> 32)) % 2^w)
  return out.toList

def lens : List Nat := (List.range 300) ++ [407, 408, 543, 544, 1000, 1087, 1088, 1089, 4096]

def main : IO Unit := do
  let mut bad := 0
  -- keccak256 / sha256 byte-level
  for n in lens do
    let m := rbytes (n+17) n
    if EA.keccak256 m != ofBA (Hash.keccak256 (toBA m)) then
      bad := bad + 1; IO.println s!"keccak256 mismatch len {n}"
    if EA.sha256 m != ofBA (Hash.sha256 (toBA m)) then
      bad := bad + 1; IO.println s!"sha256 mismatch len {n}"
  -- keccakF permutation on random states
  for i in [0:200] do
    let st := rwords (i+1) 25 64
    let a := EA.keccakF (st.map (BitVec.ofNat 64))
    let b := Hash.Keccak.Fast.keccakF (st.map (·.toUInt64)).toArray
    if a.map (·.toNat) != b.toList.map (·.toNat) then
      bad := bad + 1; IO.println s!"keccakF mismatch {i}"
  -- keccakF on short / long lists (getD 0 padding vs Fast lane getD 0)
  for k in [0, 1, 24, 26, 30] do
    let st := rwords (k+99) k 64
    let a := EA.keccakF (st.map (BitVec.ofNat 64))
    let b := Hash.Keccak.Fast.keccakF (st.map (·.toUInt64)).toArray
    IO.println s!"keccakF len {k}: accel out len {a.length}, fast out len {b.size}, eq-on-25 {a.map (·.toNat) == (b.toList.map (·.toNat)).take 25}"
  -- sha256 compression
  for i in [0:200] do
    let hs := rwords (i+3) 8 32
    let w := rwords (i+5) 16 32
    let a := EA.sha256Compress (hs.map (BitVec.ofNat 32)) (w.map (BitVec.ofNat 32))
    let b := Hash.SHA2.Reference.compress Hash.SHA2.sha256 (hs.map (BitVec.ofNat _)) (w.map (BitVec.ofNat _))
    if a.map (·.toNat) != b.map (·.toNat) then
      bad := bad + 1; IO.println s!"sha256Compress mismatch {i}"
  -- blake2b round (Accel) vs Reference.round
  for i in [0:200] do
    let v := rwords (i+7) 16 64
    let m := rwords (i+11) 16 64
    let a := EA.blake2bRound i (v.map (BitVec.ofNat 64)) (m.map (BitVec.ofNat 64))
    let b := Hash.BLAKE2.Reference.round Hash.BLAKE2.blake2bParams (m.map (BitVec.ofNat _)) (v.map (BitVec.ofNat _)) i
    if a.map (·.toNat) != b.map (·.toNat) then
      bad := bad + 1; IO.println s!"blake2bRound mismatch {i}"
  -- SpecRef Blake2b.compress vs Hash.blake2bF
  for i in [0:200] do
    let h := rwords (i+13) 8 64
    let m := rwords (i+19) 16 64
    let t := rwords (i+23) 2 64
    let rounds := [0, 1, 2, 9, 10, 11, 12, 13, 20, 24, 100].getD (i % 11) 12
    let f := i % 2 == 0
    let a := EA.Blake2b.compress rounds h m (t.getD 0 0) (t.getD 1 0) f
    let b := Hash.blake2bF rounds (h.map (·.toUInt64)).toArray (m.map (·.toUInt64)).toArray
      (t.getD 0 0).toUInt64 (t.getD 1 0).toUInt64 f
    let bBytes := b.toList.flatMap (fun w => (List.range 8).map (fun j => BitVec.ofNat 8 (w.toNat >>> (8*j))))
    if a != bBytes then
      bad := bad + 1; IO.println s!"blake2b compress mismatch {i} rounds {rounds}"
  -- RIPEMD-160: print hex for python comparison
  let mut lines : Array String := #[]
  for n in lens do
    let m := rbytes (n+31) n
    let d := EA.Ripemd160.hash m
    let hx := String.join (d.map (fun b => let s := (Nat.toDigits 16 b.toNat); String.ofList (if s.length == 1 then '0' :: s else s)))
    let mx := String.join (m.map (fun b => let s := (Nat.toDigits 16 b.toNat); String.ofList (if s.length == 1 then '0' :: s else s)))
    lines := lines.push s!"{mx} {hx}"
  IO.FS.writeFile "ripemd.txt" ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"total mismatches: {bad}"
