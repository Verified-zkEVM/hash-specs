/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

/-!
# The Keccak-p permutations: reference specification

A transcription of the Keccak-p[b, n_r] permutations of FIPS 202 §3, for every width
`b = 25 · 2^ℓ` (`ℓ ∈ {0, …, 6}`, so `b ∈ {25, 50, 100, 200, 400, 800, 1600}`) and every number of
rounds `n_r`. The state is the standard's three-dimensional array `A[x, y, z]`, represented as a
function `Fin 5 → Fin 5 → Fin w → Bool`, and the five step mappings θ, ρ, π, χ and ι are written
as in Algorithms 1–6.

This specification is meant to be read and compared with the standard. The executable
specification of Keccak-f[1600] is `Hash.Keccak.Fast`, proved equal to it in
`Hash.Keccak.Equiv`.

## References

* [FIPS 202] NIST, *SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions*,
  FIPS PUB 202, 2015. <https://doi.org/10.6028/NIST.FIPS.202>
-/

@[expose] public section

namespace Hash.Keccak

/-- A state array `A` of lane size `w`: `A x y z` is the bit `A[x, y, z]` [FIPS 202, §3.1.1]. -/
abbrev State (w : Nat) := Fin 5 → Fin 5 → Fin w → Bool

namespace State

variable {w : Nat}

/-- Converting a string to a state array [FIPS 202, §3.1.2]: `A[x, y, z] = S[w(5y + x) + z]`. -/
def ofString (w : Nat) (S : List Bool) : State w :=
  fun x y z => S.getD (w * (5 * y.val + x.val) + z.val) false

/-- `ofString` for a string stored in an array, so that reading a bit takes constant time. -/
def ofArray (w : Nat) (S : Array Bool) : State w :=
  fun x y z => S.getD (w * (5 * y.val + x.val) + z.val) false

/-- Converting a state array to a string [FIPS 202, §3.1.3]: the string is the concatenation of
the planes `y = 0, …, 4`, each the concatenation of the lanes `x = 0, …, 4`, each the bits
`z = 0, …, w − 1`. -/
def toString (A : State w) : List Bool :=
  (List.finRange 5).flatMap fun y => (List.finRange 5).flatMap fun x =>
    (List.finRange w).map fun z => A x y z

end State

/-- `(z − t) mod w`, for a position `z` within a lane of size `w`. -/
def zsub {w : Nat} (z : Fin w) (t : Nat) : Fin w :=
  ⟨(z.val + (w - t % w)) % w, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) z.isLt)⟩

variable {w : Nat}

/-! ### Step mappings [FIPS 202, §3.2] -/

/-- The column parity `C[x, z] = A[x, 0, z] ⊕ A[x, 1, z] ⊕ A[x, 2, z] ⊕ A[x, 3, z] ⊕ A[x, 4, z]`
[FIPS 202, §3.2.1, Algorithm 1, step 1]. -/
def C (A : State w) (x : Fin 5) (z : Fin w) : Bool :=
  A x 0 z ^^ A x 1 z ^^ A x 2 z ^^ A x 3 z ^^ A x 4 z

/-- `D[x, z] = C[(x − 1) mod 5, z] ⊕ C[(x + 1) mod 5, (z − 1) mod w]`
[FIPS 202, §3.2.1, Algorithm 1, step 2]. -/
def D (A : State w) (x : Fin 5) (z : Fin w) : Bool :=
  C A (x - 1) z ^^ C A (x + 1) (zsub z 1)

/-- θ: XOR each bit with the parities of two nearby columns [FIPS 202, §3.2.1, Algorithm 1]. -/
def θ (A : State w) : State w :=
  fun x y z => A x y z ^^ D A x z

/-- The lane positions `(x, y)` visited by Algorithm 2, in order: `(1, 0)` for `t = 0`, then
`(x, y) ← (y, (2x + 3y) mod 5)` [FIPS 202, §3.2.2, Algorithm 2, steps 2–3]. -/
def ρPositions : List (Fin 5 × Fin 5) :=
  (List.range 24).foldl (fun ps _ =>
    match ps.getLast? with
    | some (x, y) => ps ++ [(y, 2 * x + 3 * y)]
    | none => [(1, 0)]) [(1, 0)] |>.take 24

/-- The ρ offset of lane `(x, y)`: `(t + 1)(t + 2)/2`, where `t` is the step of Algorithm 2 at
which the lane is visited, and 0 for the lane `(0, 0)` [FIPS 202, §3.2.2, Algorithm 2]. -/
def ρOffset (x y : Fin 5) : Nat :=
  match ρPositions.idxOf? (x, y) with
  | some t => (t + 1) * (t + 2) / 2
  | none => 0

/-- ρ: rotate each lane by its offset, `A′[x, y, z] = A[x, y, (z − (t + 1)(t + 2)/2) mod w]`
[FIPS 202, §3.2.2, Algorithm 2]. -/
def ρ (A : State w) : State w :=
  fun x y z => A x y (zsub z (ρOffset x y))

/-- π: rearrange the lanes, `A′[x, y, z] = A[(x + 3y) mod 5, x, z]`
[FIPS 202, §3.2.3, Algorithm 3]. -/
def π (A : State w) : State w :=
  fun x y z => A (x + 3 * y) x z

/-- χ: the nonlinear step, `A′[x, y, z] = A[x, y, z] ⊕ ((A[(x+1) mod 5, y, z] ⊕ 1) ·
A[(x+2) mod 5, y, z])` [FIPS 202, §3.2.4, Algorithm 4]. -/
def χ (A : State w) : State w :=
  fun x y z => A x y z ^^ ((A (x + 1) y z ^^ true) && A (x + 2) y z)

/-- The linear feedback shift register of Algorithm 5, as a list of 8 bits `R[0], …, R[7]`:
one step prepends 0, XORs `R[8]` into `R[0], R[4], R[5], R[6]`, and truncates to 8 bits
[FIPS 202, §3.2.5, Algorithm 5, step 3]. -/
def rcStep (R : List Bool) : List Bool :=
  let R := false :: R
  let r8 := R.getD 8 false
  let R := R.modify 0 (· ^^ r8) |>.modify 4 (· ^^ r8) |>.modify 5 (· ^^ r8) |>.modify 6 (· ^^ r8)
  R.take 8

/-- `rc(t)`: the output bit of the LFSR after `t mod 255` steps from `10000000`
[FIPS 202, §3.2.5, Algorithm 5]. -/
def rc (t : Int) : Bool :=
  let n := (t % 255).toNat
  if n = 0 then true
  else (Nat.repeat rcStep n [true, false, false, false, false, false, false, false]).getD 0 false

/-- The round constant of round `ir` for lane size `w = 2^ℓ`: `RC[2^j − 1] = rc(j + 7 ir)` for
`j = 0, …, ℓ`, and all other bits 0 [FIPS 202, §3.2.5, Algorithm 6, steps 2–3]. -/
def RC (ℓ : Nat) (ir : Int) (z : Nat) : Bool :=
  (List.range (ℓ + 1)).any fun j => z + 1 == 2 ^ j && rc (j + 7 * ir)

/-- ι: XOR the round constant into lane `(0, 0)` [FIPS 202, §3.2.5, Algorithm 6]. Here
`w = 2^ℓ`. -/
def ι (ℓ : Nat) (A : State (2 ^ ℓ)) (ir : Int) : State (2 ^ ℓ) :=
  fun x y z => if x = 0 ∧ y = 0 then A x y z ^^ RC ℓ ir z.val else A x y z

/-- One round, `Rnd(A, i_r) = ι(χ(π(ρ(θ(A)))), i_r)` [FIPS 202, §3.3]. -/
def Rnd (ℓ : Nat) (A : State (2 ^ ℓ)) (ir : Int) : State (2 ^ ℓ) :=
  ι ℓ (χ (π (ρ (θ A)))) ir

/-- Keccak-p[b, n_r], where `b = 25 · 2^ℓ`: convert the string to a state, apply rounds
`i_r = 12 + 2ℓ − n_r, …, 12 + 2ℓ − 1`, and convert back [FIPS 202, §3.3, Algorithm 7].

For evaluation, the state is converted back to a string (stored in an array) after each round,
instead of being kept as a function, so that earlier rounds are not recomputed.
`Hash.Keccak.keccakP_eq_algorithm7` states that this is Algorithm 7 as written. -/
def keccakP (ℓ nr : Nat) (S : List Bool) : List Bool :=
  let a := (List.range nr).foldl (init := S.toArray) fun a (i : Nat) =>
    (State.toString (Rnd ℓ (State.ofArray (2 ^ ℓ) a) ((12 + 2 * ℓ : Nat) - nr + i : Int))).toArray
  a.toList

/-- Keccak-f[b] = Keccak-p[b, 12 + 2ℓ] [FIPS 202, §3.4]. -/
def keccakF (ℓ : Nat) (S : List Bool) : List Bool :=
  keccakP ℓ (12 + 2 * ℓ) S

end Hash.Keccak
