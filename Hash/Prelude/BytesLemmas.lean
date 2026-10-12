/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Prelude.BitsLemmas
public import Hash.Prelude.Bytes

/-!
# Lemmas about bytes and machine words

Facts relating the byte-level helpers of `Hash.Prelude.Bytes` (loads, stores and rotations of
`UInt32` and `UInt64` words) to bit strings and `BitVec`. They are the word-level half of the
equivalence proofs between fast and reference specifications.
-/

public section

namespace Hash

/-! ### Byte arrays as lists -/

theorem _root_.ByteArray.ext_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) :
    a = b := by
  cases a; cases b
  simp only [ByteArray.mk.injEq]
  exact Array.ext' h

theorem data_extract (b : ByteArray) (i j : Nat) :
    (b.extract i j).data.toList = (b.data.toList.drop i).take (j - i) := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract]

theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := by simp

theorem size_zeros (n : Nat) : (ByteArray.zeros n).size = n := by
  rw [size_eq_length]; simp [ByteArray.zeros]

theorem foldl_congr_mem {β γ : Type} (f g : β → γ → β) (b : β) (l : List γ)
    (h : ∀ b, ∀ x ∈ l, f b x = g b x) : l.foldl f b = l.foldl g b := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, List.foldl_cons, h b x (by simp)]
    exact ih _ fun b y hy => h b y (by simp [hy])

theorem foldl_append_bytes (ms : List ByteArray) (D : ByteArray) :
    ms.foldl (· ++ ·) D = D ++ ms.foldl (· ++ ·) ByteArray.empty := by
  induction ms generalizing D with
  | nil => exact ByteArray.ext_toList (by simp)
  | cons m ms ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (ByteArray.empty ++ m)]
    exact ByteArray.ext_toList (by simp)

/-! ### Byte lists as bit strings -/

theorem bytesToBitsMSB_take (k : Nat) (l : List UInt8) :
    bytesToBitsMSB (l.take k) = (bytesToBitsMSB l).take (8 * k) := by
  induction l generalizing k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [List.take_succ_cons, bytesToBitsMSB_cons, bytesToBitsMSB_cons, ih,
        show 8 * (k + 1) = (byteToBitsMSB x).length + 8 * k by simp; ring,
        List.take_length_add_append]

theorem bytesToBitsMSB_replicate_zero (n : Nat) :
    bytesToBitsMSB (List.replicate n 0) = List.replicate (8 * n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, bytesToBitsMSB_cons, ih, show 8 * (n + 1) = 8 + 8 * n by ring,
      ← List.replicate_append_replicate]
    rfl

theorem byteToBitsMSB_eq (b : UInt8) (n : Nat) (h : b.toNat = n % 2 ^ 8) :
    byteToBitsMSB b = natToBitsBE 8 n := by
  rw [byteToBitsMSB, h, natToBitsBE_mod]

/-- Splitting the bits of a byte list into pieces of `k` bytes. -/
theorem chunks_bytesToBitsMSB (k n : Nat) (hk : 0 < k) (l : List UInt8)
    (hl : l.length = n * k) :
    chunks (8 * k) (bytesToBitsMSB l) =
      (List.range n).map fun i => bytesToBitsMSB ((l.drop (i * k)).take k) := by
  induction n generalizing l with
  | zero =>
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this
    rfl
  | succ n ih =>
    have hlen : (l.take k).length = k :=
      List.length_take_of_le (by rw [hl]; exact Nat.le_mul_of_pos_left k (Nat.succ_pos n))
    rw [← List.take_append_drop k l, bytesToBitsMSB_append,
      chunks_append _ (by omega) _ _ (by rw [length_bytesToBitsMSB, hlen]),
      ih (l.drop k) (by rw [List.length_drop, hl, Nat.succ_mul]; omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.zero_mul, List.drop_zero,
      List.take_append_drop]
    congr 2
    funext i
    simp only [Function.comp, List.drop_drop]
    congr 3
    rw [Nat.succ_mul, Nat.add_comm]

/-- `chunks_bytesToBitsMSB` for a chunk width given as a multiple of 8. -/
theorem chunks_bytesToBitsMSB_of_eq (w k n : Nat) (hw : w = 8 * k) (hk : 0 < k)
    (l : List UInt8) (hl : l.length = n * k) :
    chunks w (bytesToBitsMSB l) =
      (List.range n).map fun i => bytesToBitsMSB ((l.drop (i * k)).take k) := by
  subst hw
  exact chunks_bytesToBitsMSB k n hk l hl

theorem drop_take_four {α : Type} (l : List α) (i : Nat) (h : i + 4 ≤ l.length) :
    (l.drop i).take 4 = [l[i], l[i + 1], l[i + 2], l[i + 3]] := by
  apply List.ext_getElem
  · simp; omega
  · intro j _ h2
    simp only [List.length_cons, List.length_nil] at h2
    simp only [List.getElem_take, List.getElem_drop]
    match j, h2 with
    | 0, _ => rfl
    | 1, _ => simp
    | 2, _ => simp
    | 3, _ => simp

theorem drop_take_eight {α : Type} (l : List α) (i : Nat) (h : i + 8 ≤ l.length) :
    (l.drop i).take 8 = [l[i], l[i + 1], l[i + 2], l[i + 3], l[i + 4], l[i + 5], l[i + 6],
      l[i + 7]] := by
  apply List.ext_getElem
  · simp; omega
  · intro j _ h2
    simp only [List.length_cons, List.length_nil] at h2
    simp only [List.getElem_take, List.getElem_drop]
    match j, h2 with
    | 0, _ => rfl
    | 1, _ => simp
    | 2, _ => simp
    | 3, _ => simp
    | 4, _ => simp
    | 5, _ => simp
    | 6, _ => simp
    | 7, _ => simp

/-! ### Big-endian bits of a number, a byte at a time -/

theorem natToBitsBE_thirtyTwo (n : Nat) : natToBitsBE 32 n =
    natToBitsBE 8 (n >>> 24) ++ natToBitsBE 8 (n >>> 16) ++ natToBitsBE 8 (n >>> 8) ++
      natToBitsBE 8 n := by
  rw [show 32 = 8 + 24 from rfl, natToBitsBE_add, show 24 = 8 + 16 from rfl, natToBitsBE_add,
    show 16 = 8 + 8 from rfl, natToBitsBE_add]
  simp [Nat.shiftRight_eq_div_pow]

theorem natToBitsBE_sixtyFour (n : Nat) : natToBitsBE 64 n =
    natToBitsBE 8 (n >>> 56) ++ natToBitsBE 8 (n >>> 48) ++ natToBitsBE 8 (n >>> 40) ++
      natToBitsBE 8 (n >>> 32) ++ natToBitsBE 8 (n >>> 24) ++ natToBitsBE 8 (n >>> 16) ++
      natToBitsBE 8 (n >>> 8) ++ natToBitsBE 8 n := by
  rw [show 64 = 8 + 56 from rfl, natToBitsBE_add, show 56 = 8 + 48 from rfl, natToBitsBE_add,
    show 48 = 8 + 40 from rfl, natToBitsBE_add, show 40 = 8 + 32 from rfl, natToBitsBE_add,
    natToBitsBE_thirtyTwo]
  simp [Nat.shiftRight_eq_div_pow]

theorem or_mul_two_pow (a b k : Nat) (hb : b < 2 ^ k) : a * 2 ^ k ||| b = a * 2 ^ k + b := by
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hb]

/-! ### `UInt32` -/

theorem UInt32.toBitVec_rotr (x : UInt32) (n : Nat) (hn : n < 32) :
    (UInt32.rotr x n.toUInt32).toBitVec = x.toBitVec.rotateRight n := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hn]
  unfold UInt32.rotr
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have h1 : (n.toUInt32).toBitVec.toNat = n := by simp; omega
    have h2 : (32 - n.toUInt32).toBitVec.toNat = 32 - n := by
      rw [UInt32.toNat_toBitVec, UInt32.toNat_sub_of_le]
      · simp; omega
      · rw [UInt32.le_iff_toNat_le]; simp; omega
    simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_umod, h1, h2]
    rw [show (32 : BitVec 32).toNat = 32 from rfl, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (by omega : 32 - n < 32)]

theorem UInt32.toBitVec_shiftRight_toUInt32 (x : UInt32) (n : Nat) (hn : n < 32) :
    (x >>> n.toUInt32).toBitVec = x.toBitVec >>> n := by
  simp [Nat.mod_eq_of_lt hn]

theorem ByteArray.toBitVec_getUInt32BE (a : ByteArray) (i : Nat) (h : i + 4 ≤ a.size) :
    (ByteArray.getUInt32BE a i).toBitVec =
      BitVec.ofNat 32 (bitsToNatBE (bytesToBitsMSB ((a.data.toList.drop i).take 4))) := by
  rw [drop_take_four _ _ (by simpa using h), bitsToNatBE_bytesToBitsMSB]
  apply BitVec.eq_of_toNat_eq
  have hs : a.size = a.data.size := rfl
  simp only [ByteArray.getUInt32BE, ByteArray.get!, List.foldl,
    UInt32.toNat_toBitVec, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    BitVec.toNat_ofNat, Array.getElem_toList,
    getElem!_pos a.data i (by omega), getElem!_pos a.data (i + 1) (by omega),
    getElem!_pos a.data (i + 2) (by omega), getElem!_pos a.data (i + 3) (by omega)]
  have h0 := a.data[i].toNat_lt
  have h1 := a.data[i + 1].toNat_lt
  have h2 := a.data[i + 2].toNat_lt
  have h3 := a.data[i + 3].toNat_lt
  generalize a.data[i].toNat = b0, a.data[i + 1].toNat = b1, a.data[i + 2].toNat = b2,
    a.data[i + 3].toNat = b3 at *
  simp only [Nat.shiftLeft_eq, UInt32.reduceToNat, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (a := b0 * 2 ^ 24) (by omega),
    Nat.mod_eq_of_lt (a := b1 * 2 ^ 16) (by omega),
    Nat.mod_eq_of_lt (a := b2 * 2 ^ 8) (by omega), Nat.or_assoc, Nat.or_assoc,
    or_mul_two_pow b2 b3 8 (by omega), or_mul_two_pow b1 _ 16 (by omega),
    or_mul_two_pow b0 _ 24 (by omega)]
  omega

theorem ByteArray.bytesToBitsMSB_pushUInt32BE (a : ByteArray) (x : UInt32) :
    bytesToBitsMSB (ByteArray.pushUInt32BE a x).data.toList =
      bytesToBitsMSB a.data.toList ++ natToBitsBE 32 x.toBitVec.toNat := by
  simp only [ByteArray.pushUInt32BE, ByteArray.data_push, Array.toList_push,
    List.append_assoc, List.cons_append, List.nil_append, bytesToBitsMSB_append,
    bytesToBitsMSB_cons, bytesToBitsMSB_nil, List.append_nil, natToBitsBE_thirtyTwo,
    UInt32.toNat_toBitVec]
  rw [byteToBitsMSB_eq _ (x.toNat >>> 24) (by simp),
    byteToBitsMSB_eq _ (x.toNat >>> 16) (by simp),
    byteToBitsMSB_eq _ (x.toNat >>> 8) (by simp), byteToBitsMSB_eq _ x.toNat (by simp)]

/-! ### `UInt64` -/

theorem UInt64.toBitVec_rotr (x : UInt64) (n : Nat) (hn : n < 64) :
    (UInt64.rotr x n.toUInt64).toBitVec = x.toBitVec.rotateRight n := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hn]
  unfold UInt64.rotr
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have h1 : (n.toUInt64).toBitVec.toNat = n := by simp; omega
    have h2 : (64 - n.toUInt64).toBitVec.toNat = 64 - n := by
      rw [UInt64.toNat_toBitVec, UInt64.toNat_sub_of_le]
      · simp; omega
      · rw [UInt64.le_iff_toNat_le]; simp; omega
    simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_umod, h1, h2]
    rw [show (64 : BitVec 64).toNat = 64 from rfl, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (by omega : 64 - n < 64)]

theorem UInt64.toBitVec_shiftRight_toUInt64 (x : UInt64) (n : Nat) (hn : n < 64) :
    (x >>> n.toUInt64).toBitVec = x.toBitVec >>> n := by
  simp [Nat.mod_eq_of_lt hn]

theorem ByteArray.toBitVec_getUInt64BE (a : ByteArray) (i : Nat) (h : i + 8 ≤ a.size) :
    (ByteArray.getUInt64BE a i).toBitVec =
      BitVec.ofNat 64 (bitsToNatBE (bytesToBitsMSB ((a.data.toList.drop i).take 8))) := by
  rw [drop_take_eight _ _ (by simpa using h), bitsToNatBE_bytesToBitsMSB]
  apply BitVec.eq_of_toNat_eq
  have hs : a.size = a.data.size := rfl
  simp only [ByteArray.getUInt64BE, ByteArray.get!, List.foldl,
    UInt64.toNat_toBitVec, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64,
    BitVec.toNat_ofNat, Array.getElem_toList,
    getElem!_pos a.data i (by omega), getElem!_pos a.data (i + 1) (by omega),
    getElem!_pos a.data (i + 2) (by omega), getElem!_pos a.data (i + 3) (by omega),
    getElem!_pos a.data (i + 4) (by omega), getElem!_pos a.data (i + 5) (by omega),
    getElem!_pos a.data (i + 6) (by omega), getElem!_pos a.data (i + 7) (by omega)]
  have h0 := a.data[i].toNat_lt
  have h1 := a.data[i + 1].toNat_lt
  have h2 := a.data[i + 2].toNat_lt
  have h3 := a.data[i + 3].toNat_lt
  have h4 := a.data[i + 4].toNat_lt
  have h5 := a.data[i + 5].toNat_lt
  have h6 := a.data[i + 6].toNat_lt
  have h7 := a.data[i + 7].toNat_lt
  generalize a.data[i].toNat = b0, a.data[i + 1].toNat = b1, a.data[i + 2].toNat = b2,
    a.data[i + 3].toNat = b3, a.data[i + 4].toNat = b4, a.data[i + 5].toNat = b5,
    a.data[i + 6].toNat = b6, a.data[i + 7].toNat = b7 at *
  simp only [Nat.shiftLeft_eq, UInt64.reduceToNat, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (a := b0 * 2 ^ 56) (by omega),
    Nat.mod_eq_of_lt (a := b1 * 2 ^ 48) (by omega),
    Nat.mod_eq_of_lt (a := b2 * 2 ^ 40) (by omega),
    Nat.mod_eq_of_lt (a := b3 * 2 ^ 32) (by omega),
    Nat.mod_eq_of_lt (a := b4 * 2 ^ 24) (by omega),
    Nat.mod_eq_of_lt (a := b5 * 2 ^ 16) (by omega),
    Nat.mod_eq_of_lt (a := b6 * 2 ^ 8) (by omega)]
  simp only [Nat.or_assoc]
  rw [or_mul_two_pow b6 b7 8 (by omega), or_mul_two_pow b5 _ 16 (by omega),
    or_mul_two_pow b4 _ 24 (by omega), or_mul_two_pow b3 _ 32 (by omega),
    or_mul_two_pow b2 _ 40 (by omega), or_mul_two_pow b1 _ 48 (by omega),
    or_mul_two_pow b0 _ 56 (by omega)]
  omega

theorem ByteArray.bytesToBitsMSB_pushUInt64BE (a : ByteArray) (x : UInt64) :
    bytesToBitsMSB (ByteArray.pushUInt64BE a x).data.toList =
      bytesToBitsMSB a.data.toList ++ natToBitsBE 64 x.toBitVec.toNat := by
  simp only [ByteArray.pushUInt64BE, ByteArray.data_push, Array.toList_push,
    List.append_assoc, List.cons_append, List.nil_append, bytesToBitsMSB_append,
    bytesToBitsMSB_cons, bytesToBitsMSB_nil, List.append_nil, natToBitsBE_sixtyFour,
    UInt64.toNat_toBitVec]
  rw [byteToBitsMSB_eq _ (x.toNat >>> 56) (by simp),
    byteToBitsMSB_eq _ (x.toNat >>> 48) (by simp),
    byteToBitsMSB_eq _ (x.toNat >>> 40) (by simp),
    byteToBitsMSB_eq _ (x.toNat >>> 32) (by simp),
    byteToBitsMSB_eq _ (x.toNat >>> 24) (by simp),
    byteToBitsMSB_eq _ (x.toNat >>> 16) (by simp),
    byteToBitsMSB_eq _ (x.toNat >>> 8) (by simp), byteToBitsMSB_eq _ x.toNat (by simp)]

end Hash
