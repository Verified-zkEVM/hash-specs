import Hash
/-! Verbatim copies: `Specs.Keccak256.roundConstants` (clean 0d76409, Clean/Specs/Keccak256.lean:8-21)
    and `Specs.Keccak256.Lanes` (clean PR #489 @253b952, Clean/Specs/Keccak256BitVec.lean:16-71). -/
namespace Specs.Keccak256
def roundConstants : Vector UInt64 24 := #v[
  0x0000000000000001, 0x0000000000008082,
  0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088,
  0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b,
  0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080,
  0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080,
  0x0000000080000001, 0x8000000080008008
]
def rotationOffsets : Vector (Vector (Fin 64) 5) 5 := #v[
  #v[0, 36, 3, 41, 18],
  #v[1, 44, 10, 45, 2],
  #v[62, 6, 43, 15, 61],
  #v[28, 55, 25, 21, 56],
  #v[27, 20, 39, 8, 14]]

/-- A Keccak-f state: lane `(x, y)` holds bits `z = 0, ..., 63`. -/
abbrev Lanes := Fin 5 → Fin 5 → BitVec 64

namespace Lanes

/-- The parity `C[x] = A[x, 0] ^ ... ^ A[x, 4]` of column `x`. -/
def columnParity (state : Lanes) (x : Fin 5) : BitVec 64 :=
  state x 0 ^^^ state x 1 ^^^ state x 2 ^^^ state x 3 ^^^ state x 4

/-- θ: `A[x, y] ^ C[x - 1] ^ rot(C[x + 1], 1)`, with `x - 1 = x + 4`. -/
def theta (state : Lanes) : Lanes := fun x y =>
  state x y ^^^ (columnParity state (x + 4) ^^^ (columnParity state (x + 1)).rotateLeft 1)

/-- ρ and π: `B[y, 2 x + 3 y] = rot(A[x, y], r[x][y])`, that is `B[x, y] = rot(A[a, x], r[a][x])`
with `a = x + 3 y`. -/
def rhoPi (state : Lanes) : Lanes := fun x y =>
  let a := x + 3 * y
  (state a x).rotateLeft rotationOffsets[a][x]

/-- χ: `B[x, y] ^ (~B[x + 1, y] & B[x + 2, y])`. -/
def chi (state : Lanes) : Lanes := fun x y =>
  state x y ^^^ (~~~state (x + 1) y &&& state (x + 2) y)

/-- ι: xor the round constant into lane `(0, 0)`. -/
def iota (state : Lanes) (roundConstant : BitVec 64) : Lanes := fun x y =>
  if x = 0 ∧ y = 0 then state x y ^^^ roundConstant else state x y

def round (state : Lanes) (roundConstant : UInt64) : Lanes :=
  iota (chi (rhoPi (theta state))) roundConstant.toBitVec

def permutation (state : Lanes) : Lanes :=
  roundConstants.foldl round state

end Lanes
end Specs.Keccak256

/-! ## Bridge: clean's `Lanes` Keccak-f is hash-specs' Keccak-p[1600, 24] -/
namespace CleanBridge
open Specs.Keccak256 Hash.Keccak

/-- The bit-level state of a `Lanes` state: `A[x][y][z]` is bit `z` of lane `(x, y)`. -/
def toRef (L : Lanes) : State 64 := fun x y z => (L x y).getLsbD z.val

theorem toRef_injective {L L' : Lanes} (h : toRef L = toRef L') : L = L' := by
  funext x y
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact congrFun (congrFun (congrFun h x) y) ⟨i, hi⟩

theorem toRef_theta (L : Lanes) : toRef (Lanes.theta L) = θ (toRef L) := by
  funext x y z
  have hz := z.isLt
  have hx4 : x + 4 = x - 1 := by revert x; decide
  have hzs : (zsub z 1).val = (z.val + 63) % 64 := by simp [zsub]
  simp only [toRef, Lanes.theta, Lanes.columnParity, θ, D, C, hx4, BitVec.getLsbD_xor,
    BitVec.getLsbD_rotateLeft, hzs]
  rcases Nat.eq_zero_or_pos z.val with h0 | h0
  · simp [h0]
  · have : (z.val + 63) % 64 = z.val - 1 := by omega
    simp [this, show ¬ z.val < 1 by omega, hz]

theorem rotationOffsets_eq (a b : Fin 5) :
    (rotationOffsets[a][b] : Nat) = ρOffset a b % 64 := by
  revert a b
  decide +kernel

theorem toRef_rhoPi (L : Lanes) : toRef (Lanes.rhoPi L) = π (ρ (toRef L)) := by
  funext x y z
  have hz := z.isLt
  simp only [toRef, Lanes.rhoPi, π, ρ, zsub, BitVec.getLsbD_rotateLeft]
  rw [show ((rotationOffsets[x + 3 * y][x] : Fin 64) : Nat) % 64 = ρOffset (x + 3 * y) x % 64 by
    rw [rotationOffsets_eq, Nat.mod_mod]]
  generalize ρOffset (x + 3 * y) x = n
  by_cases h : z.val < n % 64
  · simp [h, show (z.val + (64 - n % 64)) % 64 = 64 - n % 64 + z.val by omega]
  · simp [h, hz, show (z.val + (64 - n % 64)) % 64 = z.val - n % 64 by omega]

theorem toRef_chi (L : Lanes) : toRef (Lanes.chi L) = χ (toRef L) := by
  funext x y z
  have hz := z.isLt
  simp [toRef, Lanes.chi, χ, hz]

theorem roundConstants_getLsbD (i : Fin 24) (z : Fin 64) :
    (Specs.Keccak256.roundConstants[i]).toBitVec.getLsbD z.val = RC 6 i.val z.val := by
  revert i z
  decide +kernel

theorem toRef_iota (L : Lanes) (i : Fin 24) :
    toRef (Lanes.iota L (Specs.Keccak256.roundConstants[i]).toBitVec) = ι 6 (toRef L) i.val := by
  funext x y z
  simp only [toRef, Lanes.iota, ι]
  by_cases h : x = 0 ∧ y = 0
  · simp only [h, and_self, ↓reduceIte, BitVec.getLsbD_xor]
    rw [roundConstants_getLsbD i z]
  · simp [h]

theorem toRef_round (L : Lanes) (i : Fin 24) :
    toRef (Lanes.round L Specs.Keccak256.roundConstants[i]) = Rnd 6 (toRef L) i.val := by
  simp only [Lanes.round, Rnd, toRef_iota, toRef_chi, toRef_rhoPi, toRef_theta]

/-- clean's `Lanes.permutation` is FIPS 202 Keccak-p[1600, 24], round by round. -/
theorem toRef_permutation (L : Lanes) :
    toRef (Lanes.permutation L) =
      (List.range 24).foldl (fun A (i : Nat) => Rnd 6 A (i : Int)) (toRef L) := by
  have hrc : Specs.Keccak256.roundConstants.toList =
      (List.finRange 24).map fun i => Specs.Keccak256.roundConstants[i] := by
    decide +kernel
  simp only [Lanes.permutation, ← Vector.foldl_toList, hrc, List.foldl_map]
  rw [show List.range 24 = (List.finRange 24).map Fin.val by decide]
  rw [List.foldl_map]
  generalize List.finRange 24 = l
  induction l generalizing L with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, ← toRef_round, ih]

/-- The lanes of a hash-specs state (lane `(x, y)` at index `x + 5y`). -/
def ofFast (a : Array UInt64) : Lanes := fun x y => (Fast.lane a (x.val + 5 * y.val)).toBitVec

theorem toRef_ofFast (a : Array UInt64) : toRef (ofFast a) = Equiv.toState a := rfl

/-- **Bridge.** clean's Keccak-f (PR #489's `Lanes.permutation`) agrees with hash-specs'
`Hash.Keccak.Fast.keccakF` on every state. -/
theorem permutation_ofFast (a : Array UInt64) :
    Lanes.permutation (ofFast a) = ofFast (Fast.keccakF a) := by
  apply toRef_injective
  rw [toRef_permutation, toRef_ofFast, toRef_ofFast, Equiv.toState_keccakF]
  congr 1
  funext A i
  congr 1
  omega

end CleanBridge
