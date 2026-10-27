import Hash
def add32 (a b : ℕ) : ℕ := (a + b) % 2^32
def rotRight32 (x : ℕ) (offset : ℕ) : ℕ :=
  let offset := offset % 32
  let low := x % (2^offset)
  let high := x / (2^offset)
  low * (2^(32-offset)) + high
def Vector.mapFinRange {α} (n : ℕ) (create : Fin n → α) : Vector α n := Vector.finRange n |>.map create
def Vector.takeShort {α : Type} {n : ℕ} (v : Vector α n) (j : ℕ) (h_j : j < n) : Vector α j :=
  (v.take j).cast (by omega)
namespace Specs.SHA256

-- Round constants: first 32 bits of the fractional parts of cube roots of first 64 primes
def K : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
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
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

-- Initial hash values: first 32 bits of fractional parts of square roots of first 8 primes
def H0 : Vector ℕ 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

def not32 (a : ℕ) : ℕ := a ^^^ 0xffffffff

-- σ₀(x) = ROTR7(x) XOR ROTR18(x) XOR SHR3(x)
def lowerSigma0 (x : ℕ) : ℕ := rotRight32 x 7 ^^^ rotRight32 x 18 ^^^ (x / 2^3)

-- σ₁(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x)
def lowerSigma1 (x : ℕ) : ℕ := rotRight32 x 17 ^^^ rotRight32 x 19 ^^^ (x / 2^10)

-- Σ₀(x) = ROTR2(x) XOR ROTR13(x) XOR ROTR22(x)
def upperSigma0 (x : ℕ) : ℕ := rotRight32 x 2 ^^^ rotRight32 x 13 ^^^ rotRight32 x 22

-- Σ₁(x) = ROTR6(x) XOR ROTR11(x) XOR ROTR25(x)
def upperSigma1 (x : ℕ) : ℕ := rotRight32 x 6 ^^^ rotRight32 x 11 ^^^ rotRight32 x 25

def Ch (e f g : ℕ) : ℕ := (e &&& f) ^^^ (not32 e &&& g)

def Maj (a b c : ℕ) : ℕ := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

-- One round of the SHA-256 compression function
-- state = [a, b, c, d, e, f, g, h]
def sha256Round (state : Vector ℕ 8) (k w : ℕ) : Vector ℕ 8 :=
  let a := state[0]; let b := state[1]; let c := state[2]; let d := state[3]
  let e := state[4]; let f := state[5]; let g := state[6]; let h := state[7]
  let t1 := add32 (add32 (add32 (add32 h (upperSigma1 e)) (Ch e f g)) k) w
  let t2 := add32 (upperSigma0 a) (Maj a b c)
  #v[add32 t1 t2, a, b, c, add32 d t1, e, f, g]

-- Expand a 16-word block into a 64-word message schedule
def messageSchedule (block : Vector ℕ 16) : Vector ℕ 64 :=
  let init : Vector ℕ 64 := Vector.mapFinRange 64 fun i =>
    if h : i.val < 16 then block.get ⟨i.val, h⟩ else 0
  Fin.foldl 48 (fun w (i : Fin 48) =>
    let j := i.val + 16
    let wj := add32 (add32 (lowerSigma1 w[j - 2])  w[j - 7])
                    (add32 (lowerSigma0 w[j - 15]) w[j - 16])
    have hj   : j     < 64 := by omega
    w.set (⟨j, hj⟩ : Fin 64) wj) init

-- Apply 64 rounds of SHA-256 to the state using the message schedule
def sha256Compress (state : Vector ℕ 8) (w : Vector ℕ 64) : Vector ℕ 8 :=
  Fin.foldl 64 (fun s i => sha256Round s K[i].toNat w[i]) state

-- Process one 512-bit block (16 big-endian 32-bit words)
def compressBlock (state : Vector ℕ 8) (block : Vector ℕ 16) : Vector ℕ 8 :=
  let w := messageSchedule block
  let state' := sha256Compress state w
  Vector.mapFinRange 8 fun i => add32 state[i] state'[i]

-- Parse 4 bytes in big-endian order into a 32-bit word
def bytesToWord32BE (b0 b1 b2 b3 : ℕ) : ℕ :=
  b0 * 2^24 + b1 * 2^16 + b2 * 2^8 + b3

-- Parse 64 bytes into a block of 16 big-endian 32-bit words
def bytesToBlock (bytes : Vector ℕ 64) : Vector ℕ 16 :=
  Vector.mapFinRange 16 fun (i : Fin 16) =>
    bytesToWord32BE bytes[4 * i.val] bytes[4 * i.val + 1]
      bytes[4 * i.val + 2] bytes[4 * i.val + 3]

-- SHA-256 padding (FIPS 180-4):
--   append 0x80, then zeros until message length ≡ 56 (mod 64) bytes,
--   then the original bit length as a big-endian 64-bit integer
def pad (msg : List ℕ) : List (Vector ℕ 16) :=
  let msgLen := msg.length
  let bitLen := msgLen * 8
  let zeros  := (55 + 64 - msgLen % 64) % 64
  let padded := msg ++ [0x80] ++ List.replicate zeros 0 ++ [
    bitLen / 2^56 % 256, bitLen / 2^48 % 256,
    bitLen / 2^40 % 256, bitLen / 2^32 % 256,
    bitLen / 2^24 % 256, bitLen / 2^16 % 256,
    bitLen / 2^8  % 256, bitLen         % 256
  ]
  let numBlocks := padded.length / 64
  List.range numBlocks |>.map fun i =>
    bytesToBlock (Vector.mapFinRange 64 fun j => padded.getD (64 * i + j.val) 0)

def sha256 (msg : List ℕ) : Vector ℕ 8 :=
  (pad msg).foldl compressBlock H0

end Specs.SHA256
namespace Specs.BLAKE3

------------
-- CONSTANTS
------------

-- Default ouput length is 256 bits (32 bytes)
def outLen : ℕ := 32

-- Default key length is 256 bits (32 bytes)
def keyLen : ℕ := 32

/--
The number of input bytes in each block, i.e., 64 for all
blocks except the last block of the last chunk, which may be short.
-/
def blockLen : ℕ := 64

/--
BLAKE3 splits its input into 1024-byte chunks and arranges them
as the leaves of a binary tree.
-/
def chunkLen : ℕ := 1024

-- q Compression function doesn't seem to have an input 'd'.
-- Only the mixing function G has an input 'd'.
-- Was 'd' renamed to 'flags' in the reference implementation?
/--
The compression function input 'd' is a bitfield, with each
individual flag consisting of a power of 2. The value of 'd'
is the sum of all the flags defined for a given compression.
The following constants define their names and values:
(See Table 3 in the BLAKE3 paper.)
-/
def chunkStart : ℕ := 2^0
def chunkEnd : ℕ := 2^1
def parent : ℕ := 2^2
def root : ℕ := 2^3
def keyedHash : ℕ := 2^4
def deriveKeyContext : ℕ := 2^5
def deriveKeyMaterial : ℕ := 2^6

/--
The initialization constants for BLAKE3.
(Same as in BLAKE2s. See Table 1 in the BLAKE3 paper.)
-/
def iv : Vector UInt32 8 := #v[
  0x6a09e667,
  0xbb67ae85,
  0x3c6ef372,
  0xa54ff53a,
  0x510e527f,
  0x9b05688c,
  0x1f83d9ab,
  0x5be0cd19
]

/--
After each round (except the last one where it would be useless),
the message words are permuted according to the following
permutational key schedule for BLAKE3's keyed permutation.
(See Table 2 in the BLAKE3 paper.)
-/
def msgPermutation : Vector (Fin 16) 16 :=
--   0  1  2   3  4  5  6   7  8   9  10 11 12  13  14 15
  #v[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

------------
-- FUNCTIONS
------------

-- The mixing function, G, which mixes either a column or a diagonal.
def g (state : Vector ℕ 16) (a b c d : Fin 16) (mx my : ℕ) : Vector ℕ 16 :=
  let state_a := add32 (state[a]) (add32 state[b] mx)
  let state_d := rotRight32 (state[d] ^^^ state_a) 16
  let state_c := add32 (state[c]) state_d
  let state_b := rotRight32 (state[b] ^^^ state_c) 12

  let state_a := add32 state_a (add32 state_b my)
  let state_d := rotRight32 (state_d ^^^ state_a) 8
  let state_c := add32 state_c state_d
  let state_b := rotRight32 (state_b ^^^ state_c) 7

  state.set a state_a
        |>.set b state_b
        |>.set c state_c
        |>.set d state_d

/--
The constants a b c d for the G applications in the round, together with the indices
of the message words mx and my
-/
def roundConstants : Vector (Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16) 8 := #v[
  (0, 4, 8, 12, 0, 1),
  (1, 5, 9, 13, 2, 3),
  (2, 6, 10, 14, 4, 5),
  (3, 7, 11, 15, 6, 7),
  (0, 5, 10, 15, 8, 9),
  (1, 6, 11, 12, 10, 11),
  (2, 7, 8, 13, 12, 13),
  (3, 4, 9, 14, 14, 15)
]

/--
The round function, which applies the mixing function G
to mix the state's columns and diagonals.
-/
def round (state : Vector ℕ 16) (m : Vector ℕ 16) : Vector ℕ 16 :=
  roundConstants.foldl (fun state (a, b, c, d, i, j) =>
    g state a b c d m[i] m[j]
  ) state

/--
The permutation function, which permutes the message words after each
round (except the last one where it would be useless).
-/
def permute (state : Vector ℕ 16) : Vector ℕ 16 :=
  Vector.ofFn (fun i => state[msgPermutation[i]])

/--
Apply a single round of mixing with optional message permutation.
Used in the fold operation for applying multiple rounds.
-/
def roundWithPermute (acc : Vector ℕ 16 × Vector ℕ 16) (round_num : ℕ) : Vector ℕ 16 × Vector ℕ 16 :=
  let (state, block_words) := acc
  let new_state := round state block_words
  -- Permute block words except for the last round (round 6, 0-indexed)
  let new_block_words := if round_num < 6 then permute block_words else block_words
  (new_state, new_block_words)

/--
Apply 7 rounds of mixing to the initialized state with message permutation.
Takes chaining value, block words, counter, block length, and flags,
initializes the state, and applies the rounds using foldl.
-/
def applyRounds (chaining_value : Vector ℕ 8) (block_words : Vector ℕ 16) (counter : ℕ) (block_len : ℕ) (flags : ℕ) : Vector ℕ 16 :=
  -- Split counter into low and high parts
  let counter_low := counter % 2^32
  let counter_high := counter / 2^32

  -- Initialize state with chaining value, IV, counter, block length and flags
  let state := #v[
    chaining_value[0], chaining_value[1], chaining_value[2], chaining_value[3],
    chaining_value[4], chaining_value[5], chaining_value[6], chaining_value[7],
    iv[0].toNat, iv[1].toNat, iv[2].toNat, iv[3].toNat,
    counter_low, counter_high, block_len, flags
  ]

  let state := round state block_words
  let block_words := permute block_words
  let state := round state block_words
  let block_words := permute block_words
  let state := round state block_words
  let block_words := permute block_words
  let state := round state block_words
  let block_words := permute block_words
  let state := round state block_words
  let block_words := permute block_words
  let state := round state block_words
  let block_words := permute block_words
  let state := round state block_words

  state

/--
Final state update that XORs the first 8 words with the last 8 words,
and the last 8 words with the original chaining value.
-/
def finalStateUpdate (state : Vector ℕ 16) (chaining_value : Vector ℕ 8) : Vector ℕ 16 :=
  #v[
    state[0] ^^^ state[8],
    state[1] ^^^ state[9],
    state[2] ^^^ state[10],
    state[3] ^^^ state[11],
    state[4] ^^^ state[12],
    state[5] ^^^ state[13],
    state[6] ^^^ state[14],
    state[7] ^^^ state[15],
    chaining_value[0] ^^^ state[8],
    chaining_value[1] ^^^ state[9],
    chaining_value[2] ^^^ state[10],
    chaining_value[3] ^^^ state[11],
    chaining_value[4] ^^^ state[12],
    chaining_value[5] ^^^ state[13],
    chaining_value[6] ^^^ state[14],
    chaining_value[7] ^^^ state[15]
  ]

/--
The compression function, which takes a chaining value, block words, counter,
block length, and flags as input and produces a new state vector.
This is the core function of BLAKE3.
-/
def compress (chaining_value : Vector ℕ 8) (block_words : Vector ℕ 16) (counter : ℕ) (block_len : ℕ) (flags : ℕ) : Vector ℕ 16 :=
  let state := applyRounds chaining_value block_words counter block_len flags
  finalStateUpdate state chaining_value

--------
-- CHUNK PROCESSING
--------

/--
State maintained during chunk processing.
Tracks the current chaining value, number of blocks compressed,
and any partial block data.
-/
structure ChunkState where
  chaining_value : Vector ℕ 8      -- Current chaining value (8 × 32-bit words)
  chunk_counter : ℕ                -- Which chunk number this is
  blocks_compressed : ℕ            -- Number of blocks compressed so far
  block_buffer : List ℕ            -- Current block bytes (0-64 bytes)

/--
Initial chunk state with given chaining value and chunk counter.
-/
def initialChunkState (cv : Vector ℕ 8) (counter : ℕ) : ChunkState :=
  { chaining_value := cv
  , chunk_counter := counter
  , blocks_compressed := 0
  , block_buffer := []
  }

------------
-- Helper Functions
------------

/--
Convert a list of bytes to 32-bit words (little-endian).
Pads with zeros if less than 64 bytes.
-/
def bytesToWords (bytes : List ℕ) : Vector ℕ 16 :=
  let paddedBytes : List ℕ := bytes ++ List.replicate (64 - bytes.length) 0
  have : 64 ≤ paddedBytes.length := by
    simp only [paddedBytes, List.length_append, List.length_replicate]
    omega
  Vector.ofFn fun (i : Fin 16) =>
    let byteIdx := i.val * 4
    paddedBytes[byteIdx] +
    paddedBytes[byteIdx + 1] * 256 +
    paddedBytes[byteIdx + 2] * 256^2 +
    paddedBytes[byteIdx + 3] * 256^3

/--
Determine if CHUNK_START flag should be set based on blocks compressed.
-/
def startFlag (state : ChunkState) : ℕ :=
  if state.blocks_compressed = 0 then chunkStart else 0

------------
-- Core Processing Functions
------------

/--
Process a single block given as 16 words, updating the chunk state.
This avoids the bytes-to-words conversion when the data is already in word format.
-/
def processBlockWords (state : ChunkState) (block_words : Vector ℕ 16) : ChunkState :=
  let flags := startFlag state
  let new_cv := compress state.chaining_value block_words state.chunk_counter blockLen flags
  { state with
    chaining_value := new_cv.takeShort 8 (by omega)
    blocks_compressed := state.blocks_compressed + 1
    block_buffer := []
  }

/--
Split a list of bytes into complete blocks as words and a remainder.
Returns (complete_blocks_as_words, remainder_bytes).
Each block is returned as a Vector of 16 words.
-/
def splitIntoBlockWords (bytes : List ℕ) : (List (Vector ℕ 16) × List ℕ) :=
  splitIntoBlockWords.go bytes []
where
  /-- Tail-recursive helper function -/
  go (bytes : List ℕ) (acc : List (Vector ℕ 16)) : (List (Vector ℕ 16) × List ℕ) :=
    if bytes.length <= blockLen then
      -- If we have exactly one block worth of bytes, keep them as remainder
      -- This matches Python's behavior where a full block at the end stays in buffer
      (acc.reverse, bytes)
    else
      let blockBytes := bytes.take blockLen
      let blockWords := bytesToWords blockBytes
      let rest := bytes.drop blockLen
      go rest (blockWords :: acc)
  termination_by bytes.length
  decreasing_by
    simp only [List.length_drop, blockLen] at *
    omega

/--
Process a list of blocks given as words, updating the chunk state.
Each block is 16 words (64 bytes).
-/
def processBlocksWords (state : ChunkState) (blocks : List (Vector ℕ 16)) : ChunkState :=
  blocks.foldl processBlockWords state

/--
Main function for incremental chunk processing.
Accumulates input bytes and compresses full blocks.
-/
def updateChunk (state : ChunkState) (input_bytes : List ℕ) : ChunkState :=
  let combined := state.block_buffer ++ input_bytes
  let (blockWords, remainder) := splitIntoBlockWords combined
  let newState := processBlocksWords state blockWords
  { newState with block_buffer := remainder }

/--
Process the final block of a chunk with CHUNK_END flag.
Returns the final chaining value.
-/
def finalizeChunk (state : ChunkState) (base_flags : ℕ) : Vector ℕ 8 :=
  let block_words := bytesToWords state.block_buffer
  let flags := base_flags ||| startFlag state ||| chunkEnd
  let final_state := compress state.chaining_value block_words state.chunk_counter state.block_buffer.length flags
  final_state.take 8

/--
Process a complete chunk from start to finish.
-/
def processChunk (cv : Vector ℕ 8) (chunk_counter : ℕ) (chunk_bytes : List ℕ) (base_flags : ℕ) : Vector ℕ 8 :=
  let initial := initialChunkState cv chunk_counter
  let updated := updateChunk initial chunk_bytes
  finalizeChunk updated base_flags

end Specs.BLAKE3
def lcg (n : Nat) : Nat := (n * 6364136223846793005 + 1442695040888963407) % 2^64
def bytes (seed len : Nat) : List Nat := ((List.range len).foldl (fun (acc : List Nat × Nat) _ => let s := lcg acc.2; (acc.1 ++ [s / 2^56], s)) ([], seed)).1
def ba (l : List Nat) : ByteArray := ⟨(l.map Nat.toUInt8).toArray⟩
def wordsBE (b : ByteArray) : List Nat := (List.range (b.size / 4)).map fun i => b[4*i]!.toNat * 2^24 + b[4*i+1]!.toNat * 2^16 + b[4*i+2]!.toNat * 2^8 + b[4*i+3]!.toNat
-- SHA-256: clean `sha256` (List ℕ bytes → 8 words) vs Hash.sha256
#eval [0, 1, 3, 55, 56, 63, 64, 65, 119, 120, 200, 1000].all fun n =>
  (Specs.SHA256.sha256 (bytes n n)).toList == wordsBE (Hash.sha256 (ba (bytes n n)))
-- BLAKE3 compress: clean vs Hash.BLAKE3.Fast.compress
def rw32 (seed n : Nat) : List Nat := ((List.range n).foldl (fun (acc : List Nat × Nat) _ => let s := lcg acc.2; (acc.1 ++ [s / 2^32], s)) ([], seed)).1
#eval [1,2,3,4,5].all fun s =>
  let cv := rw32 s 8; let m := rw32 (s+100) 16
  let cvV : Vector ℕ 8 := Vector.ofFn fun i => cv.getD i.val 0
  let mV : Vector ℕ 16 := Vector.ofFn fun i => m.getD i.val 0
  let t := (lcg s) % 2^64; let b := s * 7 % 65; let d := s % 128
  (Specs.BLAKE3.compress cvV mV t b d).toList ==
    (Hash.BLAKE3.Fast.compress (cv.map Nat.toUInt32).toArray (m.map Nat.toUInt32).toArray t b d).toList.map (·.toNat)
-- BLAKE3 single chunk: clean processChunk (cv=IV, counter 0, flags 0) vs our chunkOutput.chainingValue
#eval [0, 1, 63, 64, 65, 128, 129, 1000, 1024].all fun n =>
  let iv : Vector ℕ 8 := Specs.BLAKE3.iv.map (·.toNat)
  (Specs.BLAKE3.processChunk iv 0 (bytes n n) 0).toList ==
    ((Hash.BLAKE3.Fast.chunkOutput Hash.BLAKE3.Fast.ivWords 0 0 (ba (bytes n n))).chainingValue).toList.map (·.toNat)
-- base_flags ≠ 0 (keyed hash = 16, derive-key-material = 64)
#eval [0, 1, 64, 65, 129, 1024].map fun n =>
  let iv : Vector ℕ 8 := Specs.BLAKE3.iv.map (·.toNat)
  [16, 64].map fun fl =>
  (Specs.BLAKE3.processChunk iv 0 (bytes n n) fl).toList ==
    ((Hash.BLAKE3.Fast.chunkOutput Hash.BLAKE3.Fast.ivWords fl 0 (ba (bytes n n))).chainingValue).toList.map (·.toNat)
-- multi-chunk check of chunk counter: chunk index 5
#eval [1, 64, 65, 1024].all fun n =>
  let iv : Vector ℕ 8 := Specs.BLAKE3.iv.map (·.toNat)
  (Specs.BLAKE3.processChunk iv 5 (bytes n n) 0).toList ==
    ((Hash.BLAKE3.Fast.chunkOutput Hash.BLAKE3.Fast.ivWords 0 5 (ba (bytes n n))).chainingValue).toList.map (·.toNat)
