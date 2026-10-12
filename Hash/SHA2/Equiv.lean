/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Prelude.BytesLemmas
public import Hash.SHA2.API

/-!
# SHA-2: the fast specification equals the reference

The main results say that on every byte string `m`, the byte-level SHA-2 functions of
`Hash.SHA2.API` (computed by `Hash.SHA2.Fast`) produce exactly the bits of the reference
specification `Hash.SHA2.Reference.hash` applied to the bits of `m`, for example
`Hash.SHA2.sha256_eq`.

The proof is generic in the machine-word type through `LawfulWord`, which relates a `Fast.Word`
to `BitVec w`. It has three parts: padding and parsing (bytes against bits), the compression
function (machine words against bit vectors), and the output (stores against bit strings).
-/

public section

namespace Hash.SHA2

open Fast.Word

/-- A `Fast.Word` whose operations agree with those of `BitVec w` under `toBV`. -/
class LawfulWord (α : Type) [Fast.Word α] (w : Nat) where
  /-- The bit vector a machine word denotes. -/
  toBV : α → BitVec w
  /-- The word size is one used by SHA-2. -/
  w_cases : w = 32 ∨ w = 64
  toBV_zero : toBV zero = 0
  toBV_ofNat (n : Nat) : toBV (ofNat n) = BitVec.ofNat w n
  toBV_add (x y : α) : toBV (add x y) = toBV x + toBV y
  toBV_xor (x y : α) : toBV (xor x y) = toBV x ^^^ toBV y
  toBV_and (x y : α) : toBV (and x y) = toBV x &&& toBV y
  toBV_not (x : α) : toBV (not x) = ~~~toBV x
  toBV_rotr (x : α) (n : Nat) : n < w → toBV (rotr x n) = (toBV x).rotateRight n
  toBV_shr (x : α) (n : Nat) : n < w → toBV (shr x n) = toBV x >>> n
  toBV_loadBE (p : ByteArray) (off : Nat) : off + w / 8 ≤ p.size →
    toBV (loadBE p off) =
      BitVec.ofNat w (bitsToNatBE (bytesToBitsMSB ((p.data.toList.drop off).take (w / 8))))
  bytesToBitsMSB_pushBE (a : ByteArray) (x : α) :
    bytesToBitsMSB (pushBE a x).data.toList =
      bytesToBitsMSB a.data.toList ++ natToBitsBE w (toBV x).toNat
  toBV_injective : Function.Injective toBV

instance : LawfulWord UInt32 32 where
  toBV := UInt32.toBitVec
  w_cases := .inl rfl
  toBV_zero := rfl
  toBV_ofNat _ := rfl
  toBV_add _ _ := rfl
  toBV_xor _ _ := rfl
  toBV_and _ _ := rfl
  toBV_not _ := rfl
  toBV_rotr := UInt32.toBitVec_rotr
  toBV_shr := UInt32.toBitVec_shiftRight_toUInt32
  toBV_loadBE := ByteArray.toBitVec_getUInt32BE
  bytesToBitsMSB_pushBE := ByteArray.bytesToBitsMSB_pushUInt32BE
  toBV_injective _ _ h := UInt32.toBitVec_inj.mp h

instance : LawfulWord UInt64 64 where
  toBV := UInt64.toBitVec
  w_cases := .inr rfl
  toBV_zero := rfl
  toBV_ofNat _ := rfl
  toBV_add _ _ := rfl
  toBV_xor _ _ := rfl
  toBV_and _ _ := rfl
  toBV_not _ := rfl
  toBV_rotr := UInt64.toBitVec_rotr
  toBV_shr := UInt64.toBitVec_shiftRight_toUInt64
  toBV_loadBE := ByteArray.toBitVec_getUInt64BE
  bytesToBitsMSB_pushBE := ByteArray.bytesToBitsMSB_pushUInt64BE
  toBV_injective _ _ h := UInt64.toBitVec_inj.mp h

/-- The rotation and shift amounts of `P` are less than its word size. -/
def Params.AmountsLt (P : Params) : Prop :=
  ∀ a ∈ [P.bigSigma0, P.bigSigma1, P.smallSigma0, P.smallSigma1],
    a.r₁ < P.w ∧ a.r₂ < P.w ∧ a.r₃ < P.w

instance (P : Params) : Decidable P.AmountsLt :=
  inferInstanceAs (Decidable (∀ a ∈ [P.bigSigma0, P.bigSigma1, P.smallSigma0, P.smallSigma1],
    a.r₁ < P.w ∧ a.r₂ < P.w ∧ a.r₃ < P.w))

namespace Equiv

open LawfulWord
open Reference (Vars)

/-! ### Padding and parsing -/

theorem bytesToBitsMSB_natToBytesBE (n v : Nat) :
    bytesToBitsMSB (Fast.natToBytesBE n v).data.toList = natToBitsBE (8 * n) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Fast.natToBytesBE, List.toList_toArray] at ih ⊢
    rw [List.range_succ, List.reverse_append, List.map_append, bytesToBitsMSB_append, ih,
      show 8 * (n + 1) = 8 + 8 * n by omega, natToBitsBE_add]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
      List.map_nil, bytesToBitsMSB_cons, bytesToBitsMSB_nil, List.append_nil]
    rw [byteToBitsMSB_eq _ (v / 2 ^ (8 * n)) (by simp [Nat.shiftRight_eq_div_pow])]

theorem bytesToBitsMSB_pad (P : Params) (hw : P.w = 32 ∨ P.w = 64) (m : ByteArray) :
    bytesToBitsMSB (Fast.pad P m).data.toList = Reference.pad P (bytesToBitsMSB m.data.toList) := by
  simp only [Fast.pad, Reference.pad, ByteArray.data_append, ByteArray.data_push,
    Array.toList_append, Array.toList_push, ByteArray.zeros, Array.toList_replicate,
    bytesToBitsMSB_append, bytesToBitsMSB_replicate_zero, bytesToBitsMSB_natToBytesBE,
    length_bytesToBitsMSB, bytesToBitsMSB_cons, bytesToBitsMSB_nil, List.append_nil,
    List.append_assoc, Array.length_toList, ByteArray.size_data]
  congr 1
  have hz : 7 + 8 * ((P.blockBits / 8 - (m.size + 1 + P.lengthBits / 8) % (P.blockBits / 8)) %
      (P.blockBits / 8)) = Reference.padZeros P (8 * m.size) := by
    simp only [Reference.padZeros, Params.blockBits, Params.lengthBits]
    rcases hw with h | h <;> rw [h] <;> omega
  have hl : 8 * (P.lengthBits / 8) = P.lengthBits := by
    simp only [Params.lengthBits]; rcases hw with h | h <;> rw [h]
  rw [show byteToBitsMSB 0x80 = true :: List.replicate 7 false from rfl, List.cons_append,
    List.singleton_append, ← List.append_assoc, List.replicate_append_replicate, hz, hl]

theorem size_pad (P : Params) (hw : P.w = 32 ∨ P.w = 64) (m : ByteArray) :
    (Fast.pad P m).size % (P.blockBits / 8) = 0 := by
  simp only [Fast.pad, ByteArray.size_append, ByteArray.size_push, ByteArray.zeros,
    Fast.natToBytesBE, Params.blockBits, Params.lengthBits]
  simp only [ByteArray.size, Array.size_replicate, List.size_toArray, List.length_map,
    List.length_reverse, List.length_range]
  rcases hw with h | h <;> rw [h] <;> omega

/-- The reference parse of a padded byte string, as word loads. -/
theorem parse_bytes (P : Params) (hw : P.w = 32 ∨ P.w = 64) (l : List UInt8) (N : Nat)
    (hl : l.length = N * (P.blockBits / 8)) :
    Reference.parse P (bytesToBitsMSB l) =
      (List.range N).map fun i => (List.range 16).map fun t =>
        BitVec.ofNat P.w (bitsToNatBE (bytesToBitsMSB
          ((l.drop (i * (P.blockBits / 8) + t * (P.w / 8))).take (P.w / 8)))) := by
  have hB : P.blockBits = 8 * (P.blockBits / 8) := by
    simp only [Params.blockBits]; rcases hw with h | h <;> rw [h]
  have hW : P.w = 8 * (P.w / 8) := by rcases hw with h | h <;> rw [h]
  have hBW : P.blockBits / 8 = 16 * (P.w / 8) := by
    simp only [Params.blockBits]; rcases hw with h | h <;> rw [h]
  have hk : 0 < P.w / 8 := by rcases hw with h | h <;> rw [h] <;> decide
  unfold Reference.parse
  rw [chunks_bytesToBitsMSB_of_eq _ _ N hB (by omega) l hl, List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp, List.mem_range] at hi ⊢
  rw [chunks_bytesToBitsMSB_of_eq _ (P.w / 8) 16 hW hk _ (by
      rw [List.length_take, List.length_drop, hl, ← hBW]
      have : (i + 1) * (P.blockBits / 8) ≤ N * (P.blockBits / 8) :=
        Nat.mul_le_mul_right _ hi
      rw [Nat.succ_mul] at this
      omega), List.map_map]
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp, List.mem_range] at ht ⊢
  have ht' : (t + 1) * (P.w / 8) ≤ 16 * (P.w / 8) := Nat.mul_le_mul_right _ ht
  rw [Nat.succ_mul] at ht'
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

/-! ### Words -/

section Words

variable {α : Type} [Fast.Word α] {w : Nat} [LawfulWord α w]

theorem toBV_getD (a : Array α) (i : Nat) :
    toBV (a.getD i zero) = (a.toList.map (toBV (w := w))).getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  cases a[i]? <;> simp [toBV_zero]

theorem getD_map_ofNat (l : List Nat) (t : Nat) :
    (l.map (BitVec.ofNat w)).getD t 0 = BitVec.ofNat w (l.getD t 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[t]? <;> simp

theorem toBV_Ch (x y z : α) :
    toBV (Fast.Ch x y z) = Reference.Ch (toBV x) (toBV y) (toBV (w := w) z) := by
  simp only [Fast.Ch, Reference.Ch, toBV_xor, toBV_and, toBV_not]

theorem toBV_Maj (x y z : α) :
    toBV (Fast.Maj x y z) = Reference.Maj (toBV x) (toBV y) (toBV (w := w) z) := by
  simp only [Fast.Maj, Reference.Maj, toBV_xor, toBV_and]

theorem toBV_bigSigma (a : Amounts) (h : a.r₁ < w ∧ a.r₂ < w ∧ a.r₃ < w) (x : α) :
    toBV (Fast.bigSigma a x) = Reference.bigSigma a (toBV (w := w) x) := by
  simp only [Fast.bigSigma, Reference.bigSigma, Reference.ROTR, toBV_xor,
    toBV_rotr _ _ h.1, toBV_rotr _ _ h.2.1, toBV_rotr _ _ h.2.2]

theorem toBV_smallSigma (a : Amounts) (h : a.r₁ < w ∧ a.r₂ < w ∧ a.r₃ < w) (x : α) :
    toBV (Fast.smallSigma a x) = Reference.smallSigma a (toBV (w := w) x) := by
  simp only [Fast.smallSigma, Reference.smallSigma, Reference.ROTR, Reference.SHR, toBV_xor,
    toBV_rotr _ _ h.1, toBV_rotr _ _ h.2.1, toBV_shr _ _ h.2.2]

/-- Apply a function to each working variable. -/
def mapVars {β γ : Type} (g : β → γ) (v : Vars β) : Vars γ :=
  ⟨g v.a, g v.b, g v.c, g v.d, g v.e, g v.f, g v.g, g v.h⟩

end Words

/-! ### The compression function -/

section Compress

variable {α : Type} [Fast.Word α] (P : Params) [LawfulWord α P.w]

theorem schedule_eq (hA : P.AmountsLt) (p : ByteArray) (off : Nat) (M : List (BitVec P.w))
    (hM : ∀ t < 16, toBV (loadBE (α := α) p (off + t * (P.w / 8))) = M.getD t 0) :
    (Fast.schedule (α := α) P p off).toList.map toBV = Reference.schedule P M := by
  unfold Fast.schedule Reference.schedule
  symm
  change List.foldl _ ((fun W : Array α => W.toList.map toBV)
    (Array.emptyWithCapacity P.rounds)) _ = _
  refine List.foldl_hom (fun W : Array α => W.toList.map toBV) fun W t => ?_
  simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
  congr 2
  split
  · next ht => exact (hM t ht).symm
  · simp only [toBV_add, toBV_smallSigma P.smallSigma0 (hA _ (by simp)),
      toBV_smallSigma P.smallSigma1 (hA _ (by simp)), toBV_getD]

theorem round_eq (hA : P.AmountsLt) (K W : Array α) (hK : K.toList.map toBV =
    P.K.map (BitVec.ofNat P.w)) (v : Vars α) (t : Nat) :
    Reference.round P (W.toList.map toBV) (mapVars toBV v) t =
      mapVars toBV (Fast.round P K W v t) := by
  simp only [Reference.round, Fast.round, mapVars, toBV_add, toBV_getD, hK, getD_map_ofNat,
    toBV_bigSigma P.bigSigma0 (hA _ (by simp)),
    toBV_bigSigma P.bigSigma1 (hA _ (by simp)), toBV_Ch, toBV_Maj]

theorem compress_eq (hA : P.AmountsLt) (K H : Array α)
    (hK : K.toList.map toBV = P.K.map (BitVec.ofNat P.w)) (p : ByteArray) (off : Nat)
    (M : List (BitVec P.w))
    (hM : ∀ t < 16, toBV (loadBE (α := α) p (off + t * (P.w / 8))) = M.getD t 0) :
    Reference.compress P (H.toList.map toBV) M = (Fast.compress P K H p off).toList.map toBV := by
  unfold Reference.compress Fast.compress
  rw [← schedule_eq P hA p off M hM]
  have hv : (⟨(H.toList.map toBV).getD 0 0, (H.toList.map toBV).getD 1 0,
      (H.toList.map toBV).getD 2 0, (H.toList.map toBV).getD 3 0,
      (H.toList.map toBV).getD 4 0, (H.toList.map toBV).getD 5 0,
      (H.toList.map toBV).getD 6 0, (H.toList.map toBV).getD 7 0⟩ : Vars (BitVec P.w)) =
      mapVars toBV ⟨H.getD 0 zero, H.getD 1 zero, H.getD 2 zero, H.getD 3 zero,
        H.getD 4 zero, H.getD 5 zero, H.getD 6 zero, H.getD 7 zero⟩ := by
    simp only [mapVars, toBV_getD]
  simp only []
  rw [hv, List.foldl_hom _ (round_eq P hA K _ hK)]
  simp only [mapVars, toBV_add, toBV_getD, List.map_cons, List.map_nil]

end Compress

/-! ### Output -/

section Output

variable {α : Type} [Fast.Word α] {w : Nat} [LawfulWord α w]

theorem bytesToBitsMSB_foldl_pushBE (xs : List α) (a : ByteArray) :
    bytesToBitsMSB (xs.foldl pushBE a).data.toList =
      bytesToBitsMSB a.data.toList ++
        (xs.map (toBV (w := w))).flatMap fun h => natToBitsBE w h.toNat := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, bytesToBitsMSB_pushBE (w := w), List.map_cons, List.flatMap_cons,
      List.append_assoc]

end Output

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

/-- The fast specification computes the reference specification, for any lawful word type. -/
theorem hashWith_eq {α : Type} [Fast.Word α] (P : Params) [LawfulWord α P.w]
    (hA : P.AmountsLt) (hd : P.digestBits % 8 = 0) (m : ByteArray) :
    bytesToBitsMSB (Fast.hashWith α P m).data.toList =
      Reference.hash P (bytesToBitsMSB m.data.toList) := by
  have hw : P.w = 32 ∨ P.w = 64 := LawfulWord.w_cases (α := α)
  set p := Fast.pad P m with hp
  set bb := P.blockBits / 8 with hbb
  set N := p.size / bb with hN
  have hsize : p.size = N * bb :=
    (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (size_pad P hw m))).symm
  have hBW : bb = 16 * (P.w / 8) := by
    simp only [hbb, Params.blockBits]; rcases hw with h | h <;> rw [h]
  unfold Reference.hash MerkleDamgard.iterate Fast.hashWith
  simp only []
  rw [← bytesToBitsMSB_pad P hw, ← hp, parse_bytes P hw p.data.toList N (by simpa using hsize),
    List.foldl_map]
  have hK : ((P.K.map (ofNat (α := α))).toArray).toList.map toBV =
      P.K.map (BitVec.ofNat P.w) := by
    simp [List.map_map, Function.comp_def, toBV_ofNat]
  have hH : Reference.initialHash P =
      (fun H : Array α => H.toList.map toBV) (P.H0.map (ofNat (α := α))).toArray := by
    simp [Reference.initialHash, List.map_map, Function.comp_def, toBV_ofNat]
  rw [hH, foldl_hom_of_mem (fun H : Array α => H.toList.map toBV)
    (fun H i => Fast.compress P _ H p (i * bb))]
  · rw [← Array.foldl_toList, ByteArray.data_extract, Array.toList_extract, List.extract,
      List.drop_zero, Nat.sub_zero, bytesToBitsMSB_take, bytesToBitsMSB_foldl_pushBE (w := P.w),
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd)]
    rfl
  · intro H i hi
    rw [List.mem_range] at hi
    apply compress_eq P hA _ H hK
    intro t ht
    have h1 : (i + 1) * bb ≤ N * bb := Nat.mul_le_mul_right _ hi
    have h2 : (t + 1) * (P.w / 8) ≤ 16 * (P.w / 8) := Nat.mul_le_mul_right _ ht
    rw [Nat.succ_mul] at h1 h2
    rw [toBV_loadBE _ _ (by omega), List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range ht]
    rfl

end Equiv

/-! ### The members of the family -/

theorem sha224_eq (m : ByteArray) :
    bytesToBitsMSB (Hash.sha224 m).data.toList =
      Reference.hash sha224 (bytesToBitsMSB m.data.toList) :=
  @Equiv.hashWith_eq UInt32 _ sha224 (inferInstanceAs (LawfulWord UInt32 32)) (by decide)
    (by decide) m

theorem sha256_eq (m : ByteArray) :
    bytesToBitsMSB (Hash.sha256 m).data.toList =
      Reference.hash sha256 (bytesToBitsMSB m.data.toList) :=
  @Equiv.hashWith_eq UInt32 _ sha256 (inferInstanceAs (LawfulWord UInt32 32)) (by decide)
    (by decide) m

theorem sha384_eq (m : ByteArray) :
    bytesToBitsMSB (Hash.sha384 m).data.toList =
      Reference.hash sha384 (bytesToBitsMSB m.data.toList) :=
  @Equiv.hashWith_eq UInt64 _ sha384 (inferInstanceAs (LawfulWord UInt64 64)) (by decide)
    (by decide) m

theorem sha512_eq (m : ByteArray) :
    bytesToBitsMSB (Hash.sha512 m).data.toList =
      Reference.hash sha512 (bytesToBitsMSB m.data.toList) :=
  @Equiv.hashWith_eq UInt64 _ sha512 (inferInstanceAs (LawfulWord UInt64 64)) (by decide)
    (by decide) m

theorem sha512t224_eq (m : ByteArray) :
    bytesToBitsMSB (Hash.sha512t224 m).data.toList =
      Reference.hash sha512t224 (bytesToBitsMSB m.data.toList) :=
  @Equiv.hashWith_eq UInt64 _ sha512t224 (inferInstanceAs (LawfulWord UInt64 64)) (by decide)
    (by decide) m

theorem sha512t256_eq (m : ByteArray) :
    bytesToBitsMSB (Hash.sha512t256 m).data.toList =
      Reference.hash sha512t256 (bytesToBitsMSB m.data.toList) :=
  @Equiv.hashWith_eq UInt64 _ sha512t256 (inferInstanceAs (LawfulWord UInt64 64)) (by decide)
    (by decide) m

end Hash.SHA2
