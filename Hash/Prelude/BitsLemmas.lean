/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Init
public import Hash.Prelude.Bits
public import Mathlib.Tactic.Ring

/-!
# Lemmas about bit strings

Facts about `natToBitsBE`, `bitsToNatBE`, `bytesToBitsMSB` and `chunks`, used to relate the
bit-string reference specifications to the byte-level fast specifications.
-/

public section

namespace Hash

/-! ### `natToBitsBE` and `bitsToNatBE` -/

@[simp] theorem length_natToBitsBE (w n : Nat) : (natToBitsBE w n).length = w := by
  simp [natToBitsBE]

theorem natToBitsBE_succ (w n : Nat) :
    natToBitsBE (w + 1) n = n.testBit w :: natToBitsBE w n := by
  simp [natToBitsBE, List.range_succ]

@[simp] theorem natToBitsBE_zero (n : Nat) : natToBitsBE 0 n = [] := rfl

theorem foldl_bitsToNatBE (acc : Nat) (bs : List Bool) :
    bs.foldl (fun acc b => 2 * acc + b.toNat) acc =
      acc * 2 ^ bs.length + bitsToNatBE bs := by
  induction bs generalizing acc with
  | nil => simp [bitsToNatBE]
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons, bitsToNatBE]
    rw [ih (2 * acc + b.toNat), ih (2 * 0 + b.toNat), Nat.pow_succ]
    ring

@[simp] theorem bitsToNatBE_nil : bitsToNatBE [] = 0 := rfl

theorem bitsToNatBE_append (a b : List Bool) :
    bitsToNatBE (a ++ b) = bitsToNatBE a * 2 ^ b.length + bitsToNatBE b := by
  rw [bitsToNatBE, List.foldl_append, foldl_bitsToNatBE]
  rfl

theorem bitsToNatBE_cons (x : Bool) (bs : List Bool) :
    bitsToNatBE (x :: bs) = x.toNat * 2 ^ bs.length + bitsToNatBE bs := by
  have := bitsToNatBE_append [x] bs
  simpa [bitsToNatBE] using this

theorem bitsToNatBE_lt (bs : List Bool) : bitsToNatBE bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons x bs ih =>
    rw [bitsToNatBE_cons, List.length_cons, Nat.pow_succ]
    cases x <;> simp <;> omega

theorem bitsToNatBE_natToBitsBE (w n : Nat) : bitsToNatBE (natToBitsBE w n) = n % 2 ^ w := by
  induction w with
  | zero => simp [Nat.mod_one]
  | succ w ih =>
    rw [natToBitsBE_succ, bitsToNatBE_cons, ih, length_natToBitsBE, Nat.mod_pow_succ,
      Nat.testBit_eq_decide_div_mod_eq]
    have : n / 2 ^ w % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases h : n / 2 ^ w % 2 = 1 <;> simp [h] <;> omega

theorem natToBitsBE_mod (w n : Nat) : natToBitsBE w (n % 2 ^ w) = natToBitsBE w n := by
  simp only [natToBitsBE, List.map_inj_left, List.mem_reverse, List.mem_range]
  intro i hi
  rw [Nat.testBit_mod_two_pow]
  simp [hi]

/-- `natToBitsBE` splits at any position. -/
theorem natToBitsBE_add (a b n : Nat) :
    natToBitsBE (a + b) n = natToBitsBE a (n / 2 ^ b) ++ natToBitsBE b n := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.add_right_comm, natToBitsBE_succ, ih, natToBitsBE_succ, List.cons_append,
      Nat.testBit_div_two_pow]

theorem natToBitsBE_bitsToNatBE (bs : List Bool) :
    natToBitsBE bs.length (bitsToNatBE bs) = bs := by
  induction bs with
  | nil => rfl
  | cons x bs ih =>
    have hB := bitsToNatBE_lt bs
    have hpos := Nat.two_pow_pos bs.length
    rw [bitsToNatBE_cons, List.length_cons, Nat.add_comm, natToBitsBE_add 1 bs.length]
    have h1 : (x.toNat * 2 ^ bs.length + bitsToNatBE bs) / 2 ^ bs.length = x.toNat := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hB, Nat.zero_add]
    have h2 : (x.toNat * 2 ^ bs.length + bitsToNatBE bs) % 2 ^ bs.length = bitsToNatBE bs := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hB]
    rw [h1, ← natToBitsBE_mod bs.length, h2, ih]
    cases x <;> rfl

/-! ### Bytes as bits, most significant bit first -/

@[simp] theorem length_byteToBitsMSB (b : UInt8) : (byteToBitsMSB b).length = 8 := by
  simp [byteToBitsMSB]

@[simp] theorem bytesToBitsMSB_nil : bytesToBitsMSB [] = [] := rfl

@[simp] theorem bytesToBitsMSB_cons (b : UInt8) (bs : List UInt8) :
    bytesToBitsMSB (b :: bs) = byteToBitsMSB b ++ bytesToBitsMSB bs := by
  simp [bytesToBitsMSB]

@[simp] theorem bytesToBitsMSB_append (a b : List UInt8) :
    bytesToBitsMSB (a ++ b) = bytesToBitsMSB a ++ bytesToBitsMSB b := by
  simp [bytesToBitsMSB]

@[simp] theorem length_bytesToBitsMSB (bs : List UInt8) :
    (bytesToBitsMSB bs).length = 8 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [ih]; ring

theorem bitsToNatBE_bytesToBitsMSB (bs : List UInt8) :
    bitsToNatBE (bytesToBitsMSB bs) = bs.foldl (fun acc b => 256 * acc + b.toNat) 0 := by
  suffices ∀ acc, acc * 2 ^ (8 * bs.length) + bitsToNatBE (bytesToBitsMSB bs) =
      bs.foldl (fun acc b => 256 * acc + b.toNat) acc by simpa using this 0
  induction bs with
  | nil => simp
  | cons b bs ih =>
    intro acc
    rw [List.foldl_cons, ← ih, bytesToBitsMSB_cons, bitsToNatBE_append, length_bytesToBitsMSB,
      byteToBitsMSB, bitsToNatBE_natToBitsBE, Nat.mod_eq_of_lt (by have := b.toNat_lt; omega)]
    simp only [List.length_cons]
    rw [show 8 * (bs.length + 1) = 8 + 8 * bs.length by ring, Nat.pow_add]
    ring

/-- The bits of a byte list are the big-endian bits of the number it denotes. -/
theorem bytesToBitsMSB_eq_natToBitsBE (bs : List UInt8) :
    bytesToBitsMSB bs = natToBitsBE (8 * bs.length)
      (bs.foldl (fun acc b => 256 * acc + b.toNat) 0) := by
  rw [← bitsToNatBE_bytesToBitsMSB, ← length_bytesToBitsMSB, natToBitsBE_bitsToNatBE]

/-! ### `chunks` -/

theorem chunks_go_fuel {α : Type} (n : Nat) (hn : 0 < n) (f : Nat) :
    ∀ (g : Nat) (l : List α), l.length ≤ f → l.length ≤ g →
      chunks.go n f l = chunks.go n g l := by
  induction f with
  | zero =>
    intro g l hf _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; cases g <;> rfl
  | succ f ih =>
    intro g l hf hg
    match g, l with
    | 0, l =>
      have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; rfl
    | _ + 1, [] => rfl
    | g + 1, x :: xs =>
      simp only [chunks.go]
      congr 1
      apply ih <;> simp at hf hg ⊢ <;> omega

theorem chunks_nil {α : Type} (n : Nat) : chunks n ([] : List α) = [] := rfl

theorem chunks_of_ne_nil {α : Type} (n : Nat) (hn : 0 < n) (l : List α) (hl : l ≠ []) :
    chunks n l = l.take n :: chunks n (l.drop n) := by
  match l with
  | [] => exact absurd rfl hl
  | x :: xs =>
    simp only [chunks, List.length_cons, chunks.go]
    congr 1
    exact chunks_go_fuel n hn _ _ _ (by simp; omega) le_rfl

theorem chunks_append {α : Type} (n : Nat) (hn : 0 < n) (a b : List α) (ha : a.length = n) :
    chunks n (a ++ b) = a :: chunks n b := by
  rw [chunks_of_ne_nil n hn _ (by intro h; simp_all)]
  simp [← ha]

/-- Chunks of a concatenation of equal-length pieces. -/
theorem chunks_flatten {α : Type} (n : Nat) (hn : 0 < n) (ls : List (List α))
    (h : ∀ l ∈ ls, l.length = n) : chunks n ls.flatten = ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    rw [List.flatten_cons, chunks_append n hn _ _ (h l (by simp)),
      ih (fun l hl => h l (by simp [hl]))]

/-- `chunks` as a list of slices: `⌈len / n⌉` pieces of `n` elements, the last possibly
shorter. -/
theorem chunks_eq_map_range {α : Type} (n : Nat) (hn : 0 < n) (l : List α) :
    chunks n l = (List.range ((l.length + n - 1) / n)).map fun i => (l.drop (i * n)).take n := by
  induction h : l.length using Nat.strongRecOn generalizing l with
  | _ L ih =>
    cases l with
    | nil =>
      simp only [List.length_nil] at h
      subst h
      simp [chunks_nil, hn]
    | cons x xs =>
      rw [chunks_of_ne_nil n hn _ (List.cons_ne_nil x xs),
        ih (L - n) (by simp at h; omega) _ (by simp [← h])]
      have hL : (L + n - 1) / n = (L - n + n - 1) / n + 1 := by
        by_cases hLn : L < n
        · rw [Nat.div_eq_of_lt_le (k := 1) (by simp at h; omega) (by omega),
            show L - n + n - 1 = n - 1 by omega, Nat.div_eq_of_lt (by omega)]
        · rw [show L + n - 1 = (L - n + n - 1) + n by omega, Nat.add_div_right _ hn]
      rw [hL, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Nat.zero_mul, List.drop_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp, List.drop_drop, Nat.succ_mul]
      rw [Nat.add_comm n (i * n)]

end Hash
