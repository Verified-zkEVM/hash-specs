import Hash

-- SHA3-256 Implementation in Lean4 using BitVec
-- Based on FIPS 202 specification

namespace SHA3

/-- Round constants for Keccak-f[1600] --/
def roundConstants : Array (BitVec 64) :=
  #[0x0000000000000001#64, 0x0000000000008082#64, 0x800000000000808a#64,
    0x8000000080008000#64, 0x000000000000808b#64, 0x0000000080000001#64,
    0x8000000080008081#64, 0x8000000000008009#64, 0x000000000000008a#64,
    0x0000000000000088#64, 0x0000000080008009#64, 0x000000008000000a#64,
    0x000000008000808b#64, 0x800000000000008b#64, 0x8000000000008089#64,
    0x8000000000008003#64, 0x8000000000008002#64, 0x8000000000000080#64,
    0x000000000000800a#64, 0x800000008000000a#64, 0x8000000080008081#64,
    0x8000000000008080#64, 0x0000000080000001#64, 0x8000000080008008#64]

/-- Rotation offsets for Keccak --/
def rotationOffsets : Array Nat :=
  #[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43,
    25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- State type: 5x5 array of 64-bit lanes --/
structure State where
  lanes : Vector (BitVec 64) 25
deriving BEq, Repr

/-- Create initial state --/
def State.init : State :=
  { lanes := Vector.replicate 25 0#64 }

/-- Get lane at position (x, y) --/
def State.get (s : State) (x y : Fin 5) : BitVec 64 :=
  s.lanes[y.val * 5 + x.val]

/-- Set lane at position (x, y) --/
def State.set (s : State) (x y : Fin 5) (val : BitVec 64) : State :=
  { lanes := s.lanes.set (y.val * 5 + x.val) val }

/-- Theta step --/
def theta (s : State) : State :=
  let c := Vector.ofFn fun (x : Fin 5) =>
    s.get x 0 ^^^ s.get x 1 ^^^ s.get x 2 ^^^ s.get x 3 ^^^ s.get x 4
  let d := Vector.ofFn fun (x : Fin 5) =>
    c[(x.val + 4) % 5]! ^^^ (c[(x.val + 1) % 5]!).rotateLeft 1
  let lanes := Vector.ofFn fun (i : Fin 25) =>
    let x := i.val % 5
    let y := i.val / 5
    s.get ⟨x, by omega⟩ ⟨y, by omega⟩ ^^^ d[x]
  { lanes := lanes }

def rho_pi (s : State) : State :=
  let lanes := #v[
    s.lanes[0].rotateLeft 0,
    s.lanes[6].rotateLeft 44,
    s.lanes[12].rotateLeft 43,
    s.lanes[18].rotateLeft 21,
    s.lanes[24].rotateLeft 14,
    s.lanes[3].rotateLeft 28,
    s.lanes[9].rotateLeft 20,
    s.lanes[10].rotateLeft 3,
    s.lanes[16].rotateLeft 45,
    s.lanes[22].rotateLeft 61,
    s.lanes[1].rotateLeft 1,
    s.lanes[7].rotateLeft 6,
    s.lanes[13].rotateLeft 25,
    s.lanes[19].rotateLeft 8,
    s.lanes[20].rotateLeft 18,
    s.lanes[4].rotateLeft 27,
    s.lanes[5].rotateLeft 36,
    s.lanes[11].rotateLeft 10,
    s.lanes[17].rotateLeft 15,
    s.lanes[23].rotateLeft 56,
    s.lanes[2].rotateLeft 62,
    s.lanes[8].rotateLeft 55,
    s.lanes[14].rotateLeft 39,
    s.lanes[15].rotateLeft 41,
    s.lanes[21].rotateLeft 2
  ]
  { lanes := lanes }

/-- Chi step --/
def chi (s : State) : State :=
  let lanes := #v[
    s.lanes[0] ^^^ ((~~~s.lanes[1]) &&& s.lanes[2]),
    s.lanes[1] ^^^ ((~~~s.lanes[2]) &&& s.lanes[3]),
    s.lanes[2] ^^^ ((~~~s.lanes[3]) &&& s.lanes[4]),
    s.lanes[3] ^^^ ((~~~s.lanes[4]) &&& s.lanes[0]),
    s.lanes[4] ^^^ ((~~~s.lanes[0]) &&& s.lanes[1]),
    s.lanes[5] ^^^ ((~~~s.lanes[6]) &&& s.lanes[7]),
    s.lanes[6] ^^^ ((~~~s.lanes[7]) &&& s.lanes[8]),
    s.lanes[7] ^^^ ((~~~s.lanes[8]) &&& s.lanes[9]),
    s.lanes[8] ^^^ ((~~~s.lanes[9]) &&& s.lanes[5]),
    s.lanes[9] ^^^ ((~~~s.lanes[5]) &&& s.lanes[6]),
    s.lanes[10] ^^^ ((~~~s.lanes[11]) &&& s.lanes[12]),
    s.lanes[11] ^^^ ((~~~s.lanes[12]) &&& s.lanes[13]),
    s.lanes[12] ^^^ ((~~~s.lanes[13]) &&& s.lanes[14]),
    s.lanes[13] ^^^ ((~~~s.lanes[14]) &&& s.lanes[10]),
    s.lanes[14] ^^^ ((~~~s.lanes[10]) &&& s.lanes[11]),
    s.lanes[15] ^^^ ((~~~s.lanes[16]) &&& s.lanes[17]),
    s.lanes[16] ^^^ ((~~~s.lanes[17]) &&& s.lanes[18]),
    s.lanes[17] ^^^ ((~~~s.lanes[18]) &&& s.lanes[19]),
    s.lanes[18] ^^^ ((~~~s.lanes[19]) &&& s.lanes[15]),
    s.lanes[19] ^^^ ((~~~s.lanes[15]) &&& s.lanes[16]),
    s.lanes[20] ^^^ ((~~~s.lanes[21]) &&& s.lanes[22]),
    s.lanes[21] ^^^ ((~~~s.lanes[22]) &&& s.lanes[23]),
    s.lanes[22] ^^^ ((~~~s.lanes[23]) &&& s.lanes[24]),
    s.lanes[23] ^^^ ((~~~s.lanes[24]) &&& s.lanes[20]),
    s.lanes[24] ^^^ ((~~~s.lanes[20]) &&& s.lanes[21])
  ]
  { lanes := lanes }

/-- Iota step --/
def iota (s : State) (round : Fin 24) : State :=
  let lane0 := s.get 0 0 ^^^ roundConstants[round.val]
  s.set 0 0 lane0

/-- Single round of Keccak-f[1600] --/
def keccakRound (s : State) (round : Fin 24) : State :=
  s |> theta |> rho_pi |> chi |> (iota · round)

/-- Full Keccak-f[1600] permutation (24 rounds) --/
def keccakF (s : State) : State :=
  (Array.finRange 24).foldl (fun acc i => keccakRound acc i) s

/-- Load 8 bytes in little-endian order into a UInt64 --/
def loadLittleEndian (b : ByteArray) (offset : Nat) : BitVec 64 :=
      b[offset + 7]!.toBitVec
   ++ b[offset + 6]!.toBitVec
   ++ b[offset + 5]!.toBitVec
   ++ b[offset + 4]!.toBitVec
   ++ b[offset + 3]!.toBitVec
   ++ b[offset + 2]!.toBitVec
   ++ b[offset + 1]!.toBitVec
   ++ b[offset + 0]!.toBitVec

/-- Absorb a block into the state --/
def absorb (s : State) (block : ByteArray) (rate : Nat) : State :=
  let lanes := s.lanes.mapIdx fun i lane =>
    let byteIdx := i * 8
    -- if byteIdx + 8 <= rate then
    if byteIdx < rate then
      let value := loadLittleEndian block byteIdx
      lane ^^^ value
    else
      lane
  keccakF { lanes := lanes }

/-- Pad message using pad10*1 rule for SHA3 --/
def pad101 (msg : ByteArray) (rate : Nat) : ByteArray :=
  let msgLen := msg.size
  let blockSize := rate
  -- Calculate how many bytes we need to add to reach the next block boundary
  let padLen := blockSize - (msgLen % blockSize)
  -- If only 1 byte needed, use 0x06 | 0x80 = 0x86
  if padLen == 1 then
    msg.push 0x86
  else
    let padLen := if padLen == 0 then rate else padLen
    -- First byte is 0x06 (SHA3 domain separator)
    -- Last byte is 0x80
    -- Middle bytes (if any) are 0x00
    let padded := msg.push 0x06
    let padded := (Array.range (padLen - 2)).foldl (fun acc _ => acc.push 0x00) padded
    padded.push 0x80

def squeeze (s : State) := -- : ByteArray :=
  ByteArray.mk (Array.ofFn fun (i : Fin 32) =>
    let j := i % 8;
    let x := (i.val / 8) % 5;
    let y := (i.val / (8 * 5)) % 5;
    let lane := s.get ⟨x, by omega⟩ ⟨y, by omega⟩
    ((lane >>> (j.val * 8)).toNat &&& 0xFF).toUInt8
  )

/-- SHA3-256 hash function --/
def sha3_256 (msg : ByteArray) : ByteArray :=
  let rate := 136  -- (1600 - 2*256) / 8
  let padded := pad101 msg rate
  let blocks := (padded.size + rate - 1) / rate
  let state := (Array.range blocks).foldl (fun s i =>
    let start := i * rate
    let blockEnd := min (start + rate) padded.size
    let block := padded.extract start blockEnd
    absorb s block rate
  ) State.init
  squeeze state -- 32

/-- Convert ByteArray to hex string --/
def ByteArray.toHex (ba : ByteArray) : String :=
  ba.foldl (fun acc b =>
    let hi := (b.toNat >>> 4) &&& 0xF
    let lo := b.toNat &&& 0xF
    let hiChar := if hi < 10 then Char.ofNat (hi + 48) else Char.ofNat (hi + 87)
    let loChar := if lo < 10 then Char.ofNat (lo + 48) else Char.ofNat (lo + 87)
    acc.push hiChar |>.push loChar
  ) ""

end SHA3

def toLanes (s : SHA3.State) : Array UInt64 := s.lanes.toArray.map UInt64.ofBitVec

def mkState (seed : Nat) : SHA3.State :=
  { lanes := Vector.ofFn fun (i : Fin 25) => BitVec.ofNat 64 ((seed + 1) * 0x9E3779B97F4A7C15 * (i.val + 7) ^ 5 + i.val * 0x0123456789ABCDEF) }

def msg (n seed : Nat) : ByteArray := ByteArray.mk (Array.ofFn fun (i : Fin n) => ((i.val * 31 + seed * 17 + i.val * i.val) % 256).toUInt8)

def main : IO Unit := do
  let mut bad := 0
  for seed in List.range 50 do
    let s := mkState seed
    if toLanes (SHA3.keccakF s) != Hash.Keccak.Fast.keccakF (toLanes s) then bad := bad + 1
    for r in List.range 24 do
      if toLanes (SHA3.keccakRound s ⟨r % 24, by omega⟩) != Hash.Keccak.Fast.round (toLanes s) r then bad := bad + 1
  IO.println s!"permutation/round mismatches: {bad}"
  let mut bad2 := 0
  for n in List.range 600 do
    for seed in [0, 1, 2] do
      let m := msg n seed
      if SHA3.sha3_256 m != Hash.sha3x256 m then
        bad2 := bad2 + 1
        IO.println s!"mismatch at n={n}"
  IO.println s!"sha3_256 mismatches over 1800 msgs (len 0..599): {bad2}"
  -- vendored vectors
  IO.println (SHA3.ByteArray.toHex (Hash.sha3x256 "".toUTF8))
  IO.println (SHA3.ByteArray.toHex (Hash.sha3x256 "abc".toUTF8))
  IO.println (SHA3.ByteArray.toHex (Hash.sha3x256 (ByteArray.mk (Array.replicate 200 0xa3))))
