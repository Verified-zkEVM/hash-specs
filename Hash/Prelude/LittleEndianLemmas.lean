/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Prelude.BytesLemmas

/-!
# Lemmas about little-endian bits and bytes

Facts about `natToBitsLE`, `bitsToNatLE`, `bytesToBitsLSB` and little-endian loads and stores of
`UInt32` and `UInt64` words, used to relate the reference specifications of Keccak and BLAKE2 to
their word-based fast specifications.
-/

public section

namespace Hash

/-! ### Concatenations of blocks of equal length -/

/-- Indexing a concatenation of blocks of a common length `m`. -/
theorem getElem?_flatMap_of_length {α β : Type} (l : List α) (f : α → List β) (m : Nat)
    (hf : ∀ a ∈ l, (f a).length = m) (i j : Nat) (hi : i < l.length) (hj : j < m) :
    (l.flatMap f)[i * m + j]? = (f l[i])[j]? := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.flatMap_cons]
    have ha : (f a).length = m := hf a (by simp)
    cases i with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getElem?_append_left (by omega)]
      rfl
    | succ i =>
      rw [List.getElem?_append_right (by rw [ha, Nat.succ_mul]; omega), ha,
        show (i + 1) * m + j - m = i * m + j by rw [Nat.succ_mul]; omega,
        ih (fun b hb => hf b (by simp [hb])) i (by simpa using hi)]
      rfl

theorem length_flatMap_of_length {α β : Type} (l : List α) (f : α → List β) (m : Nat)
    (hf : ∀ a ∈ l, (f a).length = m) : (l.flatMap f).length = l.length * m := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, hf a (by simp),
      ih (fun b hb => hf b (by simp [hb]))]
    simp [Nat.succ_mul, Nat.add_comm]

/-- A `foldl` homomorphism that only needs to hold on the elements of the list. -/
theorem foldl_hom_of_mem {α₁ α₂ β : Type} (f : α₁ → α₂) (g₁ : α₁ → β → α₁)
    (g₂ : α₂ → β → α₂) (l : List β) (init : α₁)
    (H : ∀ x, ∀ y ∈ l, g₂ (f x) y = f (g₁ x y)) :
    l.foldl g₂ (f init) = f (l.foldl g₁ init) := by
  induction l generalizing init with
  | nil => rfl
  | cons y l ih =>
    simp only [List.foldl_cons]
    rw [H _ _ (by simp), ih _ (fun x y hy => H x y (by simp [hy]))]

/-! ### `natToBitsLE` -/

@[simp] theorem length_natToBitsLE (w n : Nat) : (natToBitsLE w n).length = w := by
  simp [natToBitsLE]

theorem getElem?_natToBitsLE (w n z : Nat) (hz : z < w) :
    (natToBitsLE w n)[z]? = some (n.testBit z) := by
  simp [natToBitsLE, hz]

theorem natToBitsLE_add (a b n : Nat) :
    natToBitsLE (a + b) n = natToBitsLE a n ++ natToBitsLE b (n >>> a) := by
  simp only [natToBitsLE, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Nat.testBit_shiftRight]

theorem natToBitsLE_mod_two_pow (w n : Nat) : natToBitsLE w (n % 2 ^ w) = natToBitsLE w n := by
  simp only [natToBitsLE]
  apply List.map_congr_left
  intro i hi
  rw [Nat.testBit_mod_two_pow]
  simp [List.mem_range.1 hi]

/-! ### Byte lists, least significant bit first -/

@[simp] theorem length_byteToBitsLSB (b : UInt8) : (byteToBitsLSB b).length = 8 := by
  simp [byteToBitsLSB]

@[simp] theorem bytesToBitsLSB_nil : bytesToBitsLSB [] = [] := rfl

@[simp] theorem bytesToBitsLSB_cons (b : UInt8) (bs : List UInt8) :
    bytesToBitsLSB (b :: bs) = byteToBitsLSB b ++ bytesToBitsLSB bs := by
  simp [bytesToBitsLSB]

@[simp] theorem bytesToBitsLSB_append (a b : List UInt8) :
    bytesToBitsLSB (a ++ b) = bytesToBitsLSB a ++ bytesToBitsLSB b := by
  simp [bytesToBitsLSB]

@[simp] theorem length_bytesToBitsLSB (bs : List UInt8) :
    (bytesToBitsLSB bs).length = 8 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [bytesToBitsLSB_cons, List.length_append, ih,
      length_byteToBitsLSB, List.length_cons]; omega

theorem getElem?_bytesToBitsLSB (l : List UInt8) (i j : Nat) (hi : i < l.length) (hj : j < 8) :
    (bytesToBitsLSB l)[8 * i + j]? = some (l[i].toNat.testBit j) := by
  rw [bytesToBitsLSB, Nat.mul_comm, getElem?_flatMap_of_length _ _ 8 (by simp) _ _ hi hj,
    byteToBitsLSB, getElem?_natToBitsLE _ _ _ hj]

theorem bytesToBitsLSB_take (k : Nat) (l : List UInt8) :
    bytesToBitsLSB (l.take k) = (bytesToBitsLSB l).take (8 * k) := by
  induction l generalizing k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [List.take_succ_cons, bytesToBitsLSB_cons, bytesToBitsLSB_cons, ih,
        show 8 * (k + 1) = (byteToBitsLSB x).length + 8 * k by simp; omega,
        List.take_length_add_append]

theorem bytesToBitsLSB_replicate_zero (n : Nat) :
    bytesToBitsLSB (List.replicate n 0) = List.replicate (8 * n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, bytesToBitsLSB_cons, ih, show 8 * (n + 1) = 8 + 8 * n by omega,
      ← List.replicate_append_replicate]
    rfl

/-- Splitting the bits of a byte list into pieces of `k` bytes. -/
theorem chunks_bytesToBitsLSB (w k n : Nat) (hw : w = 8 * k) (hk : 0 < k) (l : List UInt8)
    (hl : l.length = n * k) :
    chunks w (bytesToBitsLSB l) =
      (List.range n).map fun i => bytesToBitsLSB ((l.drop (i * k)).take k) := by
  subst hw
  induction n generalizing l with
  | zero =>
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this
    rfl
  | succ n ih =>
    have hlen : (l.take k).length = k :=
      List.length_take_of_le (by rw [hl]; exact Nat.le_mul_of_pos_left k (Nat.succ_pos n))
    rw [← List.take_append_drop k l, bytesToBitsLSB_append,
      chunks_append _ (by omega) _ _ (by rw [length_bytesToBitsLSB, hlen]),
      ih (l.drop k) (by rw [List.length_drop, hl, Nat.succ_mul]; omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.zero_mul, List.drop_zero,
      List.take_append_drop]
    congr 2
    funext i
    simp only [Function.comp, List.drop_drop]
    congr 3
    rw [Nat.succ_mul, Nat.add_comm]

/-! ### Little-endian loads and stores of `UInt64` -/

theorem byteToBitsLSB_toUInt8 (x : UInt64) :
    byteToBitsLSB x.toUInt8 = natToBitsLE 8 x.toNat := by
  rw [byteToBitsLSB, UInt64.toNat_toUInt8, natToBitsLE_mod_two_pow]

theorem natToBitsLE_sixtyFour (n : Nat) : natToBitsLE 64 n =
    natToBitsLE 8 n ++ natToBitsLE 8 (n >>> 8) ++ natToBitsLE 8 (n >>> 16) ++
      natToBitsLE 8 (n >>> 24) ++ natToBitsLE 8 (n >>> 32) ++ natToBitsLE 8 (n >>> 40) ++
      natToBitsLE 8 (n >>> 48) ++ natToBitsLE 8 (n >>> 56) := by
  rw [show (64 : Nat) = 8 + 56 from rfl, natToBitsLE_add, show (56 : Nat) = 8 + 48 from rfl,
    natToBitsLE_add, show (48 : Nat) = 8 + 40 from rfl, natToBitsLE_add,
    show (40 : Nat) = 8 + 32 from rfl, natToBitsLE_add, show (32 : Nat) = 8 + 24 from rfl,
    natToBitsLE_add, show (24 : Nat) = 8 + 16 from rfl, natToBitsLE_add,
    show (16 : Nat) = 8 + 8 from rfl, natToBitsLE_add]
  simp only [← Nat.shiftRight_add, Nat.reduceAdd, List.append_assoc]

theorem ByteArray.bytesToBitsLSB_pushUInt64LE (a : ByteArray) (x : UInt64) :
    bytesToBitsLSB (ByteArray.pushUInt64LE a x).data.toList =
      bytesToBitsLSB a.data.toList ++ natToBitsLE 64 x.toNat := by
  simp only [ByteArray.pushUInt64LE, ByteArray.data_push, Array.toList_push,
    List.append_assoc, List.cons_append, List.nil_append, bytesToBitsLSB_append,
    bytesToBitsLSB_cons, bytesToBitsLSB_nil, List.append_nil, natToBitsLE_sixtyFour,
    byteToBitsLSB_toUInt8, UInt64.toNat_shiftRight]
  rfl

theorem UInt64.toBitVec_rotl (x : UInt64) (n : Nat) (hn : n < 64) :
    (UInt64.rotl x n.toUInt64).toBitVec = x.toBitVec.rotateLeft n := by
  rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn]
  unfold UInt64.rotl
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [BitVec.ushiftRight_eq_zero]
  · have h1 : (n.toUInt64).toBitVec.toNat = n := by simp; omega
    have h2 : (64 - n.toUInt64).toBitVec.toNat = 64 - n := by
      rw [UInt64.toNat_toBitVec, UInt64.toNat_sub_of_le]
      · simp; omega
      · rw [UInt64.le_iff_toNat_le]; simp; omega
    simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_umod, h1, h2]
    rw [show (64 : BitVec 64).toNat = 64 from rfl, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (by omega : 64 - n < 64)]

theorem ByteArray.testBit_getUInt64LE (a : ByteArray) (i z : Nat) (hz : z < 64) :
    (ByteArray.getUInt64LE a i).toNat.testBit z = (a.get! (i + z / 8)).toNat.testBit (z % 8) := by
  have hb : ∀ k, (a.get! k).toNat < 2 ^ 8 := fun k => (a.get! k).toNat_lt
  have hsh : ∀ k s, s ≤ 56 → (a.get! k).toNat <<< s % 2 ^ 64 = (a.get! k).toNat <<< s := by
    intro k s hs
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftLeft_eq]
    calc (a.get! k).toNat * 2 ^ s < 2 ^ 8 * 2 ^ s :=
          Nat.mul_lt_mul_of_pos_right (hb k) (Nat.two_pow_pos s)
      _ = 2 ^ (8 + s) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  have hhi : ∀ k j, 8 ≤ j → (a.get! k).toNat.testBit j = false := fun k j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hb k) (Nat.pow_le_pow_right (by decide) hj))
  simp only [ByteArray.getUInt64LE, UInt64.toNat_or, UInt64.toNat_shiftLeft,
    UInt8.toNat_toUInt64, UInt64.reduceToNat, Nat.reduceMod]
  rw [hsh _ _ (by decide), hsh _ _ (by decide), hsh _ _ (by decide), hsh _ _ (by decide),
    hsh _ _ (by decide), hsh _ _ (by decide), hsh _ _ (by decide)]
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have h8 : z / 8 < 8 := by omega
  rcases (show z / 8 = 0 ∨ z / 8 = 1 ∨ z / 8 = 2 ∨ z / 8 = 3 ∨ z / 8 = 4 ∨ z / 8 = 5 ∨
      z / 8 = 6 ∨ z / 8 = 7 by omega) with h | h | h | h | h | h | h | h <;>
    rw [h, show z % 8 = z - 8 * (z / 8) by omega, h] <;>
    simp (disch := omega) only [hhi, decide_eq_true, decide_eq_false, Bool.and_false,
      Bool.true_and, Bool.false_and, Bool.or_false, Bool.false_or, Nat.mul_zero, Nat.sub_zero,
      Nat.add_zero, Nat.reduceMul]

/-! ### Little-endian loads and stores of `UInt32` and `UInt64`, as bytes -/

theorem bitsToNatLE_append (a b : List Bool) :
    bitsToNatLE (a ++ b) = bitsToNatLE a + 2 ^ a.length * bitsToNatLE b := by
  induction a with
  | nil => simp [bitsToNatLE]
  | cons x a ih =>
    simp only [bitsToNatLE, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ a.length), Nat.add_assoc]

theorem bitsToNatLE_natToBitsLE (w n : Nat) : bitsToNatLE (natToBitsLE w n) = n % 2 ^ w := by
  induction w generalizing n with
  | zero => simp [natToBitsLE, bitsToNatLE, Nat.mod_one]
  | succ w ih =>
    rw [show w + 1 = 1 + w by omega, natToBitsLE_add, bitsToNatLE_append, ih, length_natToBitsLE,
      Nat.pow_add, Nat.mod_mul, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    simp only [natToBitsLE, bitsToNatLE, List.range_one, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero]
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem bitsToNatLE_bytesToBitsLSB (b : UInt8) (bs : List UInt8) :
    bitsToNatLE (bytesToBitsLSB (b :: bs)) = b.toNat + 256 * bitsToNatLE (bytesToBitsLSB bs) := by
  rw [bytesToBitsLSB_cons, bitsToNatLE_append, byteToBitsLSB, bitsToNatLE_natToBitsLE,
    length_natToBitsLE, Nat.mod_eq_of_lt b.toNat_lt]
  rfl

theorem ByteArray.toBitVec_getUInt32LE (a : ByteArray) (i : Nat) (h : i + 4 ≤ a.size) :
    (ByteArray.getUInt32LE a i).toBitVec =
      BitVec.ofNat 32 (bitsToNatLE (bytesToBitsLSB ((a.data.toList.drop i).take 4))) := by
  rw [drop_take_four _ _ (by simpa using h)]
  simp only [bitsToNatLE_bytesToBitsLSB, bytesToBitsLSB_nil]
  apply BitVec.eq_of_toNat_eq
  have hs : a.size = a.data.size := rfl
  simp only [ByteArray.getUInt32LE, ByteArray.get!,
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
  simp only [Nat.shiftLeft_eq, UInt32.reduceToNat, Nat.reduceMod, bitsToNatLE, List.foldr_nil]
  rw [Nat.mod_eq_of_lt (a := b3 * 2 ^ 24) (by omega),
    Nat.mod_eq_of_lt (a := b1 * 2 ^ 8) (by omega),
    Nat.mod_eq_of_lt (a := b2 * 2 ^ 16) (by omega), Nat.or_comm b0,
    or_mul_two_pow b1 b0 8 (by omega), Nat.or_comm (b1 * 2 ^ 8 + b0),
    or_mul_two_pow b2 _ 16 (by omega), Nat.or_comm (b2 * 2 ^ 16 + _),
    or_mul_two_pow b3 _ 24 (by omega)]
  omega

theorem ByteArray.data_pushUInt32LE (a : ByteArray) (x : UInt32) :
    (ByteArray.pushUInt32LE a x).data.toList = a.data.toList ++
      (List.range 4).map fun i => (x.toBitVec.toNat / 2 ^ (8 * i)).toUInt8 := by
  simp only [ByteArray.pushUInt32LE, ByteArray.data_push, Array.toList_push, List.append_assoc]
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append]
  simp only [List.append_cancel_left_eq, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← UInt8.toNat_inj] <;>
    simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem ByteArray.toBitVec_getUInt64LE (a : ByteArray) (i : Nat) (h : i + 8 ≤ a.size) :
    (ByteArray.getUInt64LE a i).toBitVec =
      BitVec.ofNat 64 (bitsToNatLE (bytesToBitsLSB ((a.data.toList.drop i).take 8))) := by
  rw [drop_take_eight _ _ (by simpa using h)]
  simp only [bitsToNatLE_bytesToBitsLSB, bytesToBitsLSB_nil]
  apply BitVec.eq_of_toNat_eq
  have hs : a.size = a.data.size := rfl
  simp only [ByteArray.getUInt64LE, ByteArray.get!,
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
  simp only [Nat.shiftLeft_eq, UInt64.reduceToNat, Nat.reduceMod, bitsToNatLE, List.foldr_nil]
  rw [Nat.mod_eq_of_lt (a := b1 * 2 ^ 8) (by omega),
    Nat.mod_eq_of_lt (a := b2 * 2 ^ 16) (by omega),
    Nat.mod_eq_of_lt (a := b3 * 2 ^ 24) (by omega),
    Nat.mod_eq_of_lt (a := b4 * 2 ^ 32) (by omega),
    Nat.mod_eq_of_lt (a := b5 * 2 ^ 40) (by omega),
    Nat.mod_eq_of_lt (a := b6 * 2 ^ 48) (by omega),
    Nat.mod_eq_of_lt (a := b7 * 2 ^ 56) (by omega), Nat.or_comm b0,
    or_mul_two_pow b1 b0 8 (by omega), Nat.or_comm (b1 * 2 ^ 8 + b0),
    or_mul_two_pow b2 _ 16 (by omega), Nat.or_comm (b2 * 2 ^ 16 + _),
    or_mul_two_pow b3 _ 24 (by omega), Nat.or_comm (b3 * 2 ^ 24 + _),
    or_mul_two_pow b4 _ 32 (by omega), Nat.or_comm (b4 * 2 ^ 32 + _),
    or_mul_two_pow b5 _ 40 (by omega), Nat.or_comm (b5 * 2 ^ 40 + _),
    or_mul_two_pow b6 _ 48 (by omega), Nat.or_comm (b6 * 2 ^ 48 + _),
    or_mul_two_pow b7 _ 56 (by omega)]
  omega

theorem ByteArray.data_pushUInt64LE (a : ByteArray) (x : UInt64) :
    (ByteArray.pushUInt64LE a x).data.toList = a.data.toList ++
      (List.range 8).map fun i => (x.toBitVec.toNat / 2 ^ (8 * i)).toUInt8 := by
  simp only [ByteArray.pushUInt64LE, ByteArray.data_push, Array.toList_push, List.append_assoc]
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append]
  simp only [List.append_cancel_left_eq, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← UInt8.toNat_inj] <;>
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

end Hash
