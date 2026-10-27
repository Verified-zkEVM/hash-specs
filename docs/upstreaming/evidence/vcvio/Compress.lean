import Hash
set_option maxRecDepth 4000
namespace VCVio.Algorithms.Encoding

/-- Encode a natural number in exactly `width` bytes, most significant byte first. -/
def natToBytesBE (x width : ℕ) : List UInt8 :=
  (List.range width).map (fun i => UInt8.ofNat (x / 256 ^ (width - 1 - i) % 256))


end VCVio.Algorithms.Encoding
namespace VCVio.Algorithms.Keccak

/-- ρ rotation offsets (lanes ordered `x + 5*y`). -/
def rhoLUT : Array ℕ :=
  #[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
    41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- π permutation: `(x,y) ↦ (y, 2x+3y mod 5)`, precomputed as `oldIdx ↦ newIdx`. -/
def piLUT : Array ℕ :=
  (((List.range 5).map fun y => (List.range 5).map fun x =>
    let nx := y; let ny := (2 * x + 3 * y) % 5; nx + 5 * ny).flatten).toArray

/-- Keccak-f[1600] round constants. -/
def roundConstants : Array UInt64 :=
  #[0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Left-rotate a 64-bit word by `n` bits. -/
def rotl64 (x : UInt64) (n : ℕ) : UInt64 :=
  (x <<< n.toUInt64) ||| (x >>> (64 - n).toUInt64)

/-- One Keccak-f[1600] round (θ, ρ, π, χ, ι). -/
def round (state : Array UInt64) (rc : UInt64) : Array UInt64 :=
  let C : Array UInt64 := (List.range 5).toArray.map fun x =>
    state[x]! ^^^ state[x + 5]! ^^^ state[x + 10]! ^^^ state[x + 15]! ^^^ state[x + 20]!
  let D : Array UInt64 := (List.range 5).toArray.map fun x =>
    C[(x + 4) % 5]! ^^^ rotl64 C[(x + 1) % 5]! 1
  let s1 : Array UInt64 := (List.range 25).toArray.map fun i => state[i]! ^^^ D[i % 5]!
  let B : Array UInt64 := (List.range 25).foldl
    (fun B' i => B'.set! piLUT[i]! (rotl64 s1[i]! rhoLUT[i]!)) (Array.replicate 25 0)
  let s2 : Array UInt64 := (List.range 25).toArray.map fun i =>
    let x := i % 5; let y := i / 5
    B[i]! ^^^ (~~~B[(x + 1) % 5 + 5 * y]! &&& B[(x + 2) % 5 + 5 * y]!)
  s2.set! 0 (s2[0]! ^^^ rc)

/-- The full 24-round Keccak-f[1600] permutation. -/
def f1600 (state : Array UInt64) : Array UInt64 :=
  (List.range 24).foldl (fun s r => round s roundConstants[r]!) state

/-- Sponge absorb with the given `rate` (bytes) and domain-separation pad byte. -/
def absorb (input : ByteArray) (rate : ℕ) (padByte : UInt8) : Array UInt64 := Id.run do
  let padTotal := rate - input.size % rate
  let padBytes : List UInt8 :=
    if padTotal = 1 then [padByte ||| 0x80]
    else padByte :: (List.replicate (padTotal - 2) 0 ++ [0x80])
  let padded := input ++ ByteArray.mk padBytes.toArray
  let mut s : Array UInt64 := Array.replicate 25 0
  for b in [0:padded.size / rate] do
    for i in [0:rate] do
      let bv : UInt64 := (padded[b * rate + i]!).toNat.toUInt64
      s := s.set! (i / 8) (s[i / 8]! ^^^ (bv <<< ((i % 8) * 8).toUInt64))
    s := f1600 s
  return s

/-- Squeeze the first `outLen` bytes from one state block. Callers keep `outLen ≤ rate`. -/
def squeeze (s : Array UInt64) (outLen : ℕ) : ByteArray :=
  ByteArray.mk (Array.ofFn fun i : Fin outLen =>
    ((s[i.val / 8]! >>> ((i.val % 8) * 8).toUInt64) &&& 0xFF).toUInt8)

@[simp] theorem squeeze_size (s : Array UInt64) (outLen : ℕ) :
    (squeeze s outLen).size = outLen := by
  change (Array.ofFn fun i : Fin outLen =>
    ((s[i.val / 8]! >>> ((i.val % 8) * 8).toUInt64) &&& 0xFF).toUInt8).size = outLen
  exact Array.size_ofFn

/-- Emit `blocks` complete XOF blocks and return the state for the following block. -/
def squeezeFullBlocks (initial : Array UInt64) (rate : ℕ) :
    ℕ → Array UInt64 × ByteArray
  | 0 => (initial, ByteArray.empty)
  | blocks + 1 =>
      let prior := squeezeFullBlocks initial rate blocks
      (f1600 prior.1, prior.2 ++ squeeze prior.1 rate)

@[simp] theorem squeezeFullBlocks_size (initial : Array UInt64) (rate blocks : ℕ) :
    (squeezeFullBlocks initial rate blocks).2.size = blocks * rate := by
  induction blocks with
  | zero => simp [squeezeFullBlocks]
  | succ blocks ih => simp [squeezeFullBlocks, ih, Nat.succ_mul]

/-- Multi-block XOF squeeze. Complete rate blocks are followed by the exact residual prefix.
A zero rate is outside the sponge domain and returns the empty byte array. -/
def squeezeXof (initial : Array UInt64) (rate outLen : ℕ) : ByteArray :=
  if rate = 0 then
    ByteArray.empty
  else
    let full := squeezeFullBlocks initial rate (outLen / rate)
    full.2 ++ squeeze full.1 (outLen % rate)

@[simp] theorem squeezeXof_size (initial : Array UInt64) (rate outLen : ℕ)
    (hrate : 0 < rate) :
    (squeezeXof initial rate outLen).size = outLen := by
  simp only [squeezeXof, ite_eq_right (Nat.ne_of_gt hrate), ByteArray.size_append,
    squeezeFullBlocks_size, squeeze_size]
  simpa [Nat.mul_comm] using Nat.div_add_mod outLen rate

/-- EVM `keccak256` (rate 136, pad `0x01`), 32-byte digest. -/
def keccak256 (input : ByteArray) : ByteArray := squeeze (absorb input 136 0x01) 32

/-- FIPS 202 `SHA3-256` (rate 136, pad `0x06`), 32-byte digest. -/
def sha3Digest256 (input : ByteArray) : ByteArray := squeeze (absorb input 136 0x06) 32

/-- FIPS 202 `SHA3-224` (rate 144, pad `0x06`), 28-byte digest. -/
def sha3Digest224 (input : ByteArray) : ByteArray := squeeze (absorb input 144 0x06) 28

/-- FIPS 202 `SHA3-384` (rate 104, pad `0x06`), 48-byte digest. -/
def sha3Digest384 (input : ByteArray) : ByteArray := squeeze (absorb input 104 0x06) 48

/-- FIPS 202 `SHA3-512` (rate 72, pad `0x06`), 64-byte digest. -/
def sha3Digest512 (input : ByteArray) : ByteArray := squeeze (absorb input 72 0x06) 64

/-- FIPS 202 SHAKE128 with a whole-byte output length. -/
def shake128 (input : ByteArray) (outLen : ℕ) : ByteArray :=
  squeezeXof (absorb input 168 0x1f) 168 outLen

/-- FIPS 202 SHAKE256 with a whole-byte output length. The `0x1f` delimited suffix is distinct
from both SHA3's `0x06` and Ethereum Keccak's `0x01`. -/
def shake256 (input : ByteArray) (outLen : ℕ) : ByteArray :=
  squeezeXof (absorb input 136 0x1f) 136 outLen

@[simp] theorem shake128_size (input : ByteArray) (outLen : ℕ) :
    (shake128 input outLen).size = outLen := by
  simp [shake128]

@[simp] theorem shake256_size (input : ByteArray) (outLen : ℕ) :
    (shake256 input outLen).size = outLen := by
  simp [shake256]

@[simp] theorem sha3Digest224_size (input : ByteArray) : (sha3Digest224 input).size = 28 := by
  simp [sha3Digest224]

@[simp] theorem sha3Digest256_size (input : ByteArray) : (sha3Digest256 input).size = 32 := by
  simp [sha3Digest256]

@[simp] theorem sha3Digest384_size (input : ByteArray) : (sha3Digest384 input).size = 48 := by
  simp [sha3Digest384]

@[simp] theorem sha3Digest512_size (input : ByteArray) : (sha3Digest512 input).size = 64 := by
  simp [sha3Digest512]

end VCVio.Algorithms.Keccak
namespace VCVio.Algorithms.Sha2

/-- The eight SHA-256 initial hash values `H₀…H₇`. -/
def iv : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The eight SHA-224 initial hash values. -/
def iv224 : Array UInt32 :=
  #[0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
    0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4]

/-- The 64 SHA-256 round constants `K₀…K₆₃`. -/
def k : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Right rotation of a 32-bit word. -/
def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- `Ch(x,y,z) = (x∧y) ⊕ (¬x∧z)`. -/
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj(x,y,z) = (x∧y) ⊕ (x∧z) ⊕ (y∧z)`. -/
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ₀(x)`. -/
def bsig0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
/-- `Σ₁(x)`. -/
def bsig1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
/-- `σ₀(x)`. -/
def ssig0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
/-- `σ₁(x)`. -/
def ssig1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- Eight working registers of one SHA-256 compression round. -/
structure RoundState where
  /-- First working register, in the standard state order. -/
  a : UInt32
  /-- Second working register, in the standard state order. -/
  b : UInt32
  /-- Third working register, in the standard state order. -/
  c : UInt32
  /-- Fourth working register, in the standard state order. -/
  d : UInt32
  /-- Fifth working register, in the standard state order. -/
  e : UInt32
  /-- Sixth working register, in the standard state order. -/
  f : UInt32
  /-- Seventh working register, in the standard state order. -/
  g : UInt32
  /-- Eighth working register, in the standard state order. -/
  h : UInt32
  deriving DecidableEq, Repr

/-- One SHA-256 round, parameterized by its constant and schedule word. -/
def round256 (s : RoundState) (kt wt : UInt32) : RoundState :=
  let t1 := s.h + bsig1 s.e + ch s.e s.f s.g + kt + wt
  let t2 := bsig0 s.a + maj s.a s.b s.c
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- Big-endian 4-byte serialization of a 32-bit word. -/
def u32be (x : UInt32) : ByteArray :=
  ByteArray.mk #[(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- Big-endian 8-byte serialization of a 64-bit word. -/
def u64be (x : UInt64) : ByteArray :=
  ByteArray.mk #[(x >>> 56).toUInt8, (x >>> 48).toUInt8, (x >>> 40).toUInt8, (x >>> 32).toUInt8,
    (x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- SHA-256 padding (FIPS 180-4 §5.1.1): append `0x80`, zero-pad, then the 64-bit big-endian
bit length, to a multiple of 64 bytes. -/
def pad (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let bitLen : UInt64 := (len.toUInt64) * 8
  let mut out := msg.push 0x80
  let zeros := (56 + 64 - (len + 1) % 64) % 64
  for _ in [0:zeros] do
    out := out.push 0
  return out ++ u64be bitLen

/-- Load one big-endian word from a block at an arbitrary byte offset. -/
def readWord256 (m : ByteArray) (base t : Nat) : UInt32 :=
  let o := base + t * 4
  (m[o]!).toUInt32 <<< 24 ||| (m[o + 1]!).toUInt32 <<< 16 |||
    (m[o + 2]!).toUInt32 <<< 8 ||| (m[o + 3]!).toUInt32

/-- Load the first sixteen schedule entries into the 64-word buffer. -/
def loadSchedule256 (m : ByteArray) (base : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.replicate 64 0
  for t in [0:16] do
    w := w.set! t (readWord256 m base t)
  return w

/-- Expand the remaining 48 schedule entries in place. -/
def expandSchedule256 (initial : Array UInt32) : Array UInt32 := Id.run do
  let mut w := initial
  for t in [16:64] do
    w := w.set! t (ssig1 (w[t - 2]!) + w[t - 7]! + ssig0 (w[t - 15]!) + w[t - 16]!)
  return w

/-- Run all 64 rounds from the selected chaining state and expanded schedule. -/
def runRounds256 (st w : Array UInt32) : RoundState := Id.run do
  let mut s : RoundState := ⟨st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!⟩
  for t in [0:64] do
    s := round256 s k[t]! w[t]!
  return s

/-- Add the final working registers to the incoming chaining state. -/
def feedForward256 (st : Array UInt32) (s : RoundState) : Array UInt32 :=
  #[st[0]! + s.a, st[1]! + s.b, st[2]! + s.c, st[3]! + s.d,
    st[4]! + s.e, st[5]! + s.f, st[6]! + s.g, st[7]! + s.h]

/-- Process one 64-byte block at offset `base`, updating the 8-word state `st`. -/
def compress (st : Array UInt32) (m : ByteArray) (base : Nat) : Array UInt32 :=
  feedForward256 st (runRounds256 st (expandSchedule256 (loadSchedule256 m base)))

/-- Serialize the eight-word SHA-224/SHA-256 state to exactly 32 bytes. -/
def stateBytes32 (st : Array UInt32) : ByteArray :=
  ByteArray.mk (Array.ofFn fun i : Fin 32 => (u32be st[i.val / 4]!)[i.val % 4]!)

@[simp] theorem stateBytes32_size (st : Array UInt32) : (stateBytes32 st).size = 32 := by
  change (Array.ofFn fun i : Fin 32 => (u32be st[i.val / 4]!)[i.val % 4]!).size = 32
  exact Array.size_ofFn

/-- Run the SHA-256 compression function from a selected initial state and serialize `outLen`
digest bytes. This is the common FIPS 180-4 engine for SHA-224 and SHA-256. -/
def sha256Family (initial : Array UInt32) (outLen : ℕ)
    (msg : ByteArray) : ByteArray := Id.run do
  let padded := pad msg
  let mut st := initial
  for b in [0:padded.size / 64] do
    st := compress st padded (b * 64)
  return (stateBytes32 st).extract 0 outLen

/-- SHA-224 of a byte string (28-byte digest). -/
def sha224 (msg : ByteArray) : ByteArray := sha256Family iv224 28 msg

/-- SHA-256 of a byte string (32-byte digest). -/
def sha256 (msg : ByteArray) : ByteArray := sha256Family iv 32 msg

@[simp] theorem sha224_size (msg : ByteArray) : (sha224 msg).size = 28 := by
  simp [sha224, sha256Family]

@[simp] theorem sha256_size (msg : ByteArray) : (sha256 msg).size = 32 := by
  simp [sha256, sha256Family]

/-- MGF1 with SHA-256 (RFC 8017 §B.2.1): expand `seed` to `outLen` bytes. -/
def mgf1 (seed : ByteArray) (outLen : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let blocks := (outLen + 31) / 32
  for ctr in [0:blocks] do
    out := out ++ sha256 (seed ++ u32be ctr.toUInt32)
  return out.extract 0 outLen

/-- Zero-pad (or hash-then-pad) a key to the 64-byte SHA-256 block. -/
def hmacKey0 (key : ByteArray) : ByteArray := Id.run do
  let k := if key.size > 64 then sha256 key else key
  let mut out := k
  for _ in [0:64 - k.size] do
    out := out.push 0
  return out

/-- XOR every byte of a 64-byte block with a constant. -/
def xorConst (block : ByteArray) (c : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:block.size] do
    out := out.push (block[i]! ^^^ c)
  return out

/-- HMAC-SHA256 (FIPS 198-1) of `msg` under `key`. -/
def hmacSha256 (key msg : ByteArray) : ByteArray :=
  let k0 := hmacKey0 key
  sha256 (xorConst k0 0x5c ++ sha256 (xorConst k0 0x36 ++ msg))

/-! ## SHA-512 -/

/-- The eight SHA-512 initial hash values `H₀…H₇`. -/
def iv512 : Array UInt64 :=
  #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- The eight SHA-384 initial hash values. -/
def iv384 : Array UInt64 :=
  #[0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
    0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4]

/-- The eight SHA-512/224 initial hash values. -/
def iv512Trunc224 : Array UInt64 :=
  #[0x8c3d37c819544da2, 0x73e1996689dcd4d6, 0x1dfab7ae32ff9c82, 0x679dd514582f9fcf,
    0x0f6d2b697bd44da8, 0x77e36f7304c48942, 0x3f9d85a86a1d36c8, 0x1112e6ad91d692a1]

/-- The eight SHA-512/256 initial hash values. -/
def iv512Trunc256 : Array UInt64 :=
  #[0x22312194fc2bf72c, 0x9f555fa3c84c64c2, 0x2393b86b6f53b151, 0x963877195940eabd,
    0x96283ee2a88effe3, 0xbe5e1e2553863992, 0x2b0199fc2c85b8aa, 0x0eb72ddc81c52ca2]

/-- The 80 SHA-512 round constants. -/
def k512 : Array UInt64 :=
  #[0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- Right rotation of a 64-bit word. -/
def rotr64 (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- SHA-512 `Ch`. -/
def ch64 (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (~~~x &&& z)

/-- SHA-512 `Maj`. -/
def maj64 (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- SHA-512 `Σ₀`. -/
def bsig0Sha512 (x : UInt64) : UInt64 := rotr64 x 28 ^^^ rotr64 x 34 ^^^ rotr64 x 39

/-- SHA-512 `Σ₁`. -/
def bsig1Sha512 (x : UInt64) : UInt64 := rotr64 x 14 ^^^ rotr64 x 18 ^^^ rotr64 x 41

/-- SHA-512 `σ₀`. -/
def ssig0Sha512 (x : UInt64) : UInt64 := rotr64 x 1 ^^^ rotr64 x 8 ^^^ (x >>> 7)

/-- SHA-512 `σ₁`. -/
def ssig1Sha512 (x : UInt64) : UInt64 := rotr64 x 19 ^^^ rotr64 x 61 ^^^ (x >>> 6)

/-- SHA-512 padding: `1`, zeroes, and a 128-bit big-endian bit length. -/
def pad512 (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let mut out := msg.push 0x80
  let zeros := (112 + 128 - (len + 1) % 128) % 128
  for _ in [0:zeros] do
    out := out.push 0
  return out ++ ByteArray.mk (Encoding.natToBytesBE (8 * len) 16).toArray

/-- Process one 128-byte SHA-512 block. -/
def compress512 (st : Array UInt64) (m : ByteArray)
    (base : Nat) : Array UInt64 := Id.run do
  let mut w : Array UInt64 := Array.replicate 80 0
  for t in [0:16] do
    let o := base + t * 8
    let word : UInt64 :=
      (m[o]!).toUInt64 <<< 56 ||| (m[o + 1]!).toUInt64 <<< 48 |||
      (m[o + 2]!).toUInt64 <<< 40 ||| (m[o + 3]!).toUInt64 <<< 32 |||
      (m[o + 4]!).toUInt64 <<< 24 ||| (m[o + 5]!).toUInt64 <<< 16 |||
      (m[o + 6]!).toUInt64 <<< 8 ||| (m[o + 7]!).toUInt64
    w := w.set! t word
  for t in [16:80] do
    w := w.set! t (ssig1Sha512 (w[t - 2]!) + w[t - 7]! + ssig0Sha512 (w[t - 15]!) + w[t - 16]!)
  let mut a := st[0]!
  let mut b := st[1]!
  let mut c := st[2]!
  let mut d := st[3]!
  let mut e := st[4]!
  let mut f := st[5]!
  let mut g := st[6]!
  let mut h := st[7]!
  for t in [0:80] do
    let t1 := h + bsig1Sha512 e + ch64 e f g + k512[t]! + w[t]!
    let t2 := bsig0Sha512 a + maj64 a b c
    h := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[st[0]! + a, st[1]! + b, st[2]! + c, st[3]! + d,
    st[4]! + e, st[5]! + f, st[6]! + g, st[7]! + h]

/-- Serialize the eight-word SHA-384/SHA-512 state to exactly 64 bytes. -/
def stateBytes64 (st : Array UInt64) : ByteArray :=
  ByteArray.mk (Array.ofFn fun i : Fin 64 => (u64be st[i.val / 8]!)[i.val % 8]!)

@[simp] theorem stateBytes64_size (st : Array UInt64) : (stateBytes64 st).size = 64 := by
  change (Array.ofFn fun i : Fin 64 => (u64be st[i.val / 8]!)[i.val % 8]!).size = 64
  exact Array.size_ofFn

/-- Run the SHA-512 compression function from a selected initial state and serialize `outLen`
digest bytes. This is the common FIPS 180-4 engine for the SHA-384 and SHA-512 variants. -/
def sha512Family (initial : Array UInt64) (outLen : ℕ)
    (msg : ByteArray) : ByteArray := Id.run do
  let padded := pad512 msg
  let mut st := initial
  for b in [0:padded.size / 128] do
    st := compress512 st padded (b * 128)
  return (stateBytes64 st).extract 0 outLen

/-- SHA-384 of a byte string (48-byte digest). -/
def sha384 (msg : ByteArray) : ByteArray := sha512Family iv384 48 msg

/-- SHA-512 of a byte string (64-byte digest). -/
def sha512 (msg : ByteArray) : ByteArray := sha512Family iv512 64 msg

/-- SHA-512/224 of a byte string (28-byte digest). -/
def sha512Trunc224 (msg : ByteArray) : ByteArray := sha512Family iv512Trunc224 28 msg

/-- SHA-512/256 of a byte string (32-byte digest). -/
def sha512Trunc256 (msg : ByteArray) : ByteArray := sha512Family iv512Trunc256 32 msg

@[simp] theorem sha384_size (msg : ByteArray) : (sha384 msg).size = 48 := by
  simp [sha384, sha512Family]

@[simp] theorem sha512_size (msg : ByteArray) : (sha512 msg).size = 64 := by
  simp [sha512, sha512Family]

@[simp] theorem sha512Trunc224_size (msg : ByteArray) : (sha512Trunc224 msg).size = 28 := by
  simp [sha512Trunc224, sha512Family]

@[simp] theorem sha512Trunc256_size (msg : ByteArray) : (sha512Trunc256 msg).size = 32 := by
  simp [sha512Trunc256, sha512Family]

/-- MGF1 with SHA-512. -/
def mgf1Sha512 (seed : ByteArray) (outLen : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let blocks := (outLen + 63) / 64
  for ctr in [0:blocks] do
    out := out ++ sha512 (seed ++ u32be ctr.toUInt32)
  return out.extract 0 outLen

/-- The explicit SHA-256 name, parallel to `mgf1Sha512`; `mgf1` remains a compatibility alias. -/
def mgf1Sha256 (seed : ByteArray) (outLen : Nat) : ByteArray := mgf1 seed outLen

/-- Zero-pad (or hash-then-pad) a key to the 128-byte SHA-512 block. -/
def hmacKey0Sha512 (key : ByteArray) : ByteArray := Id.run do
  let k := if key.size > 128 then sha512 key else key
  let mut out := k
  for _ in [0:128 - k.size] do
    out := out.push 0
  return out

/-- HMAC-SHA-512. -/
def hmacSha512 (key msg : ByteArray) : ByteArray :=
  let k0 := hmacKey0Sha512 key
  sha512 (xorConst k0 0x5c ++ sha512 (xorConst k0 0x36 ++ msg))

/-! ## Checked standard-domain boundaries -/

/-- Rejections at the SHA-2 and MGF1 standard-domain boundary. -/
inductive InputError where
  | messageTooLong (algorithm : String) (sizeBytes maximumExclusive : ℕ)
  | maskTooLong (algorithm : String) (requested maximum : ℕ)
deriving Repr, DecidableEq

/-- SHA-256's 64-bit length field admits messages shorter than `2^61` bytes. -/
def sha256InputLengthValid (sizeBytes : ℕ) : Bool := sizeBytes < 2 ^ 61

/-- SHA-512's 128-bit length field admits messages shorter than `2^125` bytes. -/
def sha512InputLengthValid (sizeBytes : ℕ) : Bool := sizeBytes < 2 ^ 125

/-- Reject a SHA-256 input outside FIPS 180-4's 64-bit bit-length domain. -/
def sha256Checked (msg : ByteArray) : Except InputError ByteArray :=
  if sha256InputLengthValid msg.size then
    .ok (sha256 msg)
  else
    .error (.messageTooLong "SHA-256" msg.size (2 ^ 61))

/-- Reject a SHA-512 input outside FIPS 180-4's 128-bit bit-length domain. -/
def sha512Checked (msg : ByteArray) : Except InputError ByteArray :=
  if sha512InputLengthValid msg.size then
    .ok (sha512 msg)
  else
    .error (.messageTooLong "SHA-512" msg.size (2 ^ 125))

/-- RFC 8017's maximum MGF1-SHA-256 output length. -/
def mgf1Sha256Maximum : ℕ := 2 ^ 32 * 32

/-- RFC 8017's maximum MGF1-SHA-512 output length. -/
def mgf1Sha512Maximum : ℕ := 2 ^ 32 * 64

/-- MGF1-SHA-256 with the RFC 8017 counter-wrap bound checked before execution. -/
def mgf1Sha256Checked (seed : ByteArray) (outLen : ℕ) : Except InputError ByteArray :=
  if outLen ≤ mgf1Sha256Maximum then
    .ok (mgf1Sha256 seed outLen)
  else
    .error (.maskTooLong "MGF1-SHA-256" outLen mgf1Sha256Maximum)

/-- MGF1-SHA-512 with the RFC 8017 counter-wrap bound checked before execution. -/
def mgf1Sha512Checked (seed : ByteArray) (outLen : ℕ) : Except InputError ByteArray :=
  if outLen ≤ mgf1Sha512Maximum then
    .ok (mgf1Sha512 seed outLen)
  else
    .error (.maskTooLong "MGF1-SHA-512" outLen mgf1Sha512Maximum)

end VCVio.Algorithms.Sha2
open VCVio.Algorithms
def K32 : Array UInt32 := (Hash.SHA2.sha256.K.map Hash.SHA2.Fast.Word.ofNat).toArray
def K64 : Array UInt64 := (Hash.SHA2.sha512.K.map Hash.SHA2.Fast.Word.ofNat).toArray
def gen (seed len : Nat) : ByteArray :=
  ByteArray.mk ((List.range len).map fun i => ((seed * 131 + i * 7 + i*i) % 256).toUInt8).toArray
def main : IO Unit := do
  let mut ok := true
  for i in [0:200] do
    let st : Array UInt32 := (Array.range 8).map fun j => (j * 2654435761 + i * 97).toUInt32
    let st64 : Array UInt64 := (Array.range 8).map fun j => (j * 0x9E3779B97F4A7C15 + i * 97).toUInt64
    let m := gen i (64 + i % 200)
    let base := i % (m.size - 63)
    ok := ok && Sha2.compress st m base == Hash.SHA2.Fast.compress Hash.SHA2.sha256 K32 st m base
    let m2 := gen i (128 + i % 200)
    let base2 := i % (m2.size - 127)
    ok := ok && Sha2.compress512 st64 m2 base2 == Hash.SHA2.Fast.compress Hash.SHA2.sha512 K64 st64 m2 base2
    let x : UInt32 := (i * 2654435761 + 12345).toUInt32
    ok := ok && Sha2.bsig0 x == Hash.SHA2.Fast.bigSigma Hash.SHA2.sha256.bigSigma0 x
      && Sha2.ssig1 x == Hash.SHA2.Fast.smallSigma Hash.SHA2.sha256.smallSigma1 x
    -- rotr at out-of-range amounts
  ok := ok && (K32.toList == Sha2.k.toList) && (K64.toList == Sha2.k512.toList)
  -- VCVio's rotr at n = 0 (outside the documented domain)
  IO.println s!"compress/sigma/K agree: {ok}; VCVio rotr x 0 = {Sha2.rotr 0x80000001 0}, Hash rotr x 0 = {Hash.SHA2.Fast.Word.rotr (0x80000001 : UInt32) 0}"
  -- VCVio Keccak rotl64 at n = 0
  IO.println s!"VCVio rotl64 x 0 = {Keccak.rotl64 0x8000000000000001 0}"
  -- compress with short state arrays
  let st5 : Array UInt32 := #[1,2,3,4,5]
  IO.println s!"short-state compress agree: {Sha2.compress st5 (gen 1 64) 0 == Hash.SHA2.Fast.compress Hash.SHA2.sha256 K32 st5 (gen 1 64) 0}"
  IO.println s!"compress past end agree: {Sha2.compress #[1,2,3,4,5,6,7,8] (gen 1 70) 30 == Hash.SHA2.Fast.compress Hash.SHA2.sha256 K32 #[1,2,3,4,5,6,7,8] (gen 1 70) 30}"
