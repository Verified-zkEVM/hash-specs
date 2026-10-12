/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Prelude.LittleEndianLemmas
public import Hash.BLAKE2.API

/-!
# BLAKE2: the fast specification equals the reference

The main results say that the byte-level BLAKE2 functions of `Hash.BLAKE2.API` (computed by
`Hash.BLAKE2.Fast`) produce exactly the bytes of the reference specification
`Hash.BLAKE2.Reference.hash`, for every key of at most one block, salt, personalisation, output
length and message: `Hash.BLAKE2.blake2bWith_eq` and `Hash.BLAKE2.blake2sWith_eq`. The
compression function behind the EIP-152 precompile is the reference `F` for any number of rounds
(`Hash.BLAKE2.blake2bF_eq`).

The proof is generic in the machine-word type through `LawfulWord`, which relates a `Fast.Word`
to `BitVec w`. Arrays of machine words correspond to lists of bit vectors by `toBV`, and each step
of the fast specification maps to the same step of the reference.
-/

public section

namespace Hash.BLAKE2

open Fast.Word

/-- A `Fast.Word` whose operations agree with those of `BitVec w` under `toBV`. -/
class LawfulWord (α : Type) [Fast.Word α] (w : Nat) where
  /-- The bit vector a machine word denotes. -/
  toBV : α → BitVec w
  toBV_zero : toBV zero = 0
  toBV_ofNat (n : Nat) : toBV (ofNat n) = BitVec.ofNat w n
  toBV_add (x y : α) : toBV (add x y) = toBV x + toBV y
  toBV_xor (x y : α) : toBV (xor x y) = toBV x ^^^ toBV y
  toBV_not (x : α) : toBV (not x) = ~~~toBV x
  toBV_rotr (x : α) (n : Nat) : n < w → toBV (rotr x n) = (toBV x).rotateRight n
  toBV_loadLE (p : ByteArray) (off : Nat) : off + w / 8 ≤ p.size →
    toBV (loadLE p off) =
      BitVec.ofNat w (bitsToNatLE (bytesToBitsLSB ((p.data.toList.drop off).take (w / 8))))
  data_pushLE (a : ByteArray) (x : α) :
    (pushLE a x).data.toList =
      a.data.toList ++ (List.range (w / 8)).map fun i => ((toBV x).toNat / 2 ^ (8 * i)).toUInt8

instance : LawfulWord UInt32 32 where
  toBV := UInt32.toBitVec
  toBV_zero := rfl
  toBV_ofNat _ := rfl
  toBV_add _ _ := rfl
  toBV_xor _ _ := rfl
  toBV_not _ := rfl
  toBV_rotr := UInt32.toBitVec_rotr
  toBV_loadLE := ByteArray.toBitVec_getUInt32LE
  data_pushLE := ByteArray.data_pushUInt32LE

instance : LawfulWord UInt64 64 where
  toBV := UInt64.toBitVec
  toBV_zero := rfl
  toBV_ofNat _ := rfl
  toBV_add _ _ := rfl
  toBV_xor _ _ := rfl
  toBV_not _ := rfl
  toBV_rotr := UInt64.toBitVec_rotr
  toBV_loadLE := ByteArray.toBitVec_getUInt64LE
  data_pushLE := ByteArray.data_pushUInt64LE

/-- The shape facts about `P` that the proof uses: whole-byte words, rotations shorter than a
word, sixteen-word blocks, an eight-word IV and parameter block. -/
def Params.Valid (P : Params) : Prop :=
  8 * (P.w / 8) = P.w ∧ 0 < P.w / 8 ∧
  P.R.1 < P.w ∧ P.R.2.1 < P.w ∧ P.R.2.2.1 < P.w ∧ P.R.2.2.2 < P.w ∧
  P.blockBytes = 16 * (P.w / 8) ∧ P.IV.length = 8 ∧
  4 ≤ P.saltOffset ∧ P.saltOffset + 2 * P.saltBytes = 8 * (P.w / 8)

instance (P : Params) : Decidable P.Valid :=
  inferInstanceAs (Decidable (8 * (P.w / 8) = P.w ∧ 0 < P.w / 8 ∧
    P.R.1 < P.w ∧ P.R.2.1 < P.w ∧ P.R.2.2.1 < P.w ∧ P.R.2.2.2 < P.w ∧
    P.blockBytes = 16 * (P.w / 8) ∧ P.IV.length = 8 ∧
    4 ≤ P.saltOffset ∧ P.saltOffset + 2 * P.saltBytes = 8 * (P.w / 8)))

theorem blake2bParams_valid : blake2bParams.Valid := by decide

theorem blake2sParams_valid : blake2sParams.Valid := by decide

namespace Equiv

open LawfulWord

variable {α : Type} [Fast.Word α] (P : Params) [LawfulWord α P.w]

/-- An array of machine words as the list of bit vectors it denotes. -/
abbrev bv (v : Array α) : List (BitVec P.w) := v.toList.map toBV

theorem toBV_get (v : Array α) (i : Nat) : toBV (Fast.get v i) = (bv P v).getD i 0 := by
  rw [Fast.get, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  cases v[i]? <;> simp [toBV_zero]

theorem bv_set! (v : Array α) (i : Nat) (x : α) :
    bv P (v.set! i x) = (bv P v).set i (toBV x) := by
  simp [bv, Array.set!, List.map_set]

theorem bv_toArray (l : List α) : bv P l.toArray = l.map toBV := by
  simp [bv]

theorem bv_append (a b : Array α) : bv P (a ++ b) = bv P a ++ bv P b := by
  simp [bv]

theorem G_eq (hR : P.R.1 < P.w ∧ P.R.2.1 < P.w ∧ P.R.2.2.1 < P.w ∧ P.R.2.2.2 < P.w)
    (v : Array α) (a b c d : Nat) (x y : α) :
    bv P (Fast.G P v a b c d x y) = Reference.G P (bv P v) a b c d (toBV x) (toBV y) := by
  rcases hP : P.R with ⟨R1, R2, R3, R4⟩
  rw [hP] at hR
  obtain ⟨h1, h2, h3, h4⟩ := hR
  simp only [Fast.G, Reference.G, hP, bv_set!, toBV_get, toBV_add, toBV_xor, toBV_rotr _ _ h1,
    toBV_rotr _ _ h2, toBV_rotr _ _ h3, toBV_rotr _ _ h4]

theorem round_eq (hR : P.R.1 < P.w ∧ P.R.2.1 < P.w ∧ P.R.2.2.1 < P.w ∧ P.R.2.2.2 < P.w)
    (m v : Array α) (i : Nat) :
    bv P (Fast.round P m v i) = Reference.round P (bv P m) (bv P v) i := by
  simp only [Fast.round, Reference.round, G_eq P hR, toBV_get]

theorem F_eq (hR : P.R.1 < P.w ∧ P.R.2.1 < P.w ∧ P.R.2.2.1 < P.w ∧ P.R.2.2.2 < P.w)
    (rounds : Nat) (h m : Array α) (t : Nat) (f : Bool) :
    bv P (Fast.F P rounds h m t f) = Reference.F P rounds (bv P h) (bv P m) t f := by
  have hfold : ∀ (l : List Nat) (v : Array α),
      bv P (l.foldl (Fast.round P m) v) = l.foldl (Reference.round P (bv P m)) (bv P v) := by
    intro l
    induction l with
    | nil => intro v; rfl
    | cons i l ih => intro v; simp only [List.foldl_cons, ih, round_eq P hR]
  simp only [Fast.F, Reference.F, bv_toArray, List.map_map, Function.comp_def, toBV_xor,
    toBV_get, hfold]
  congr
  funext i
  cases f <;> simp only [bv_set!, toBV_get, toBV_xor, toBV_ofNat, toBV_not, bv_append,
    bv_toArray, List.map_map, Function.comp_def, Bool.false_eq_true, ↓reduceIte]

/-! ### Bytes and words -/

/-- Chunks of a list whose length is a multiple of the chunk size. -/
theorem chunks_eq_range {β : Type} (n N : Nat) (hn : 0 < n) (l : List β) (hl : l.length = N * n) :
    chunks n l = (List.range N).map fun i => (l.drop (i * n)).take n := by
  induction N generalizing l with
  | zero =>
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this
    rfl
  | succ N ih =>
    have hlen : (l.take n).length = n :=
      List.length_take_of_le (by rw [hl]; exact Nat.le_mul_of_pos_left n (Nat.succ_pos N))
    rw [← List.take_append_drop n l, chunks_append _ hn _ _ hlen,
      ih (l.drop n) (by rw [List.length_drop, hl, Nat.succ_mul]; omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.zero_mul, List.drop_zero, List.take_append_drop]
    congr 2
    funext i
    simp only [Function.comp, List.drop_drop]
    congr 3
    rw [Nat.succ_mul, Nat.add_comm]

/-- The words of a byte string of `N` whole words, as loads. -/
theorem wordsLE_eq (hw : 0 < P.w / 8) (l : List UInt8) (N : Nat) (hl : l.length = N * (P.w / 8)) :
    Reference.wordsLE P l = (List.range N).map fun j =>
      BitVec.ofNat P.w
        (bitsToNatLE (bytesToBitsLSB ((l.drop (j * (P.w / 8))).take (P.w / 8)))) := by
  rw [Reference.wordsLE, chunks_eq_range _ N hw l hl, List.map_map]
  rfl

theorem block_eq (hP : P.Valid) (p : ByteArray) (off : Nat) (h : off + P.blockBytes ≤ p.size) :
    bv P (Fast.block (α := α) P p off) =
      Reference.wordsLE P ((p.data.toList.drop off).take P.blockBytes) := by
  obtain ⟨_, hk, _, _, _, _, hbb, _⟩ := hP
  have hs : p.size = p.data.toList.length := by simp
  rw [wordsLE_eq P hk _ 16 (by rw [List.length_take, List.length_drop, ← hs]; omega),
    Fast.block, bv_toArray, List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp, List.mem_range] at hj ⊢
  have hj' : (j + 1) * (P.w / 8) ≤ 16 * (P.w / 8) := Nat.mul_le_mul_right _ hj
  rw [Nat.succ_mul] at hj'
  rw [toBV_loadLE _ _ (by omega), List.drop_take, List.take_take, List.drop_drop,
    Nat.min_eq_left (by omega), Nat.add_comm]

/-- Storing words one after another gives their little-endian bytes. -/
theorem data_foldl_pushLE (h : Array α) (a : ByteArray) :
    (h.foldl pushLE a).data.toList = a.data.toList ++ (bv P h).flatMap (Reference.bytesLE P) := by
  rw [← Array.foldl_toList, bv]
  induction h.toList generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, data_pushLE (w := P.w), List.map_cons, List.flatMap_cons,
      List.append_assoc]
    rfl

theorem data_extract_zero (b : ByteArray) (d : Nat) :
    (b.extract 0 d).data.toList = b.data.toList.take d := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract, List.drop_zero, Nat.sub_zero]

theorem init_eq (hP : P.Valid) (pb : ByteArray) (hpb : pb.size = 8 * (P.w / 8)) :
    bv P (((List.range 8).map fun i =>
        xor (ofNat (P.IV.getD i 0)) (loadLE pb (i * (P.w / 8)))).toArray : Array α) =
      List.zipWith (· ^^^ ·) (P.IV.map (BitVec.ofNat P.w))
        (Reference.wordsLE P pb.data.toList) := by
  obtain ⟨_, hk, _, _, _, _, _, hIV, _⟩ := hP
  have hs : pb.size = pb.data.toList.length := by simp
  rw [wordsLE_eq P hk _ 8 (by omega), bv_toArray, List.map_map]
  apply List.ext_getElem
  · simp [hIV]
  · intro i h1 _
    simp only [List.length_map, List.length_range] at h1
    have hi : (i + 1) * (P.w / 8) ≤ 8 * (P.w / 8) := Nat.mul_le_mul_right _ h1
    rw [Nat.succ_mul] at hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, Function.comp,
      toBV_xor, toBV_ofNat, toBV_loadLE _ _ (by omega : i * (P.w / 8) + P.w / 8 ≤ pb.size),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < P.IV.length),
      Option.getD_some]

/-- The message padding makes whole blocks. -/
theorem exists_pad_eq (ll bb : Nat) (hb : 0 < bb) : ∃ M, ll + (bb - ll % bb) % bb = M * bb := by
  have h1 := Nat.div_add_mod ll bb
  have h2 := Nat.mod_lt ll hb
  by_cases h : ll % bb = 0
  · exact ⟨ll / bb, by rw [h, Nat.sub_zero, Nat.mod_self, Nat.mul_comm]; omega⟩
  · refine ⟨ll / bb + 1, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega : bb - ll % bb < bb), Nat.succ_mul, Nat.mul_comm]
    omega

theorem data_pad (key msg : ByteArray) :
    (Fast.pad P key msg).data.toList =
      let pre := (if key.size = 0 then [] else
          key.data.toList ++ List.replicate (P.blockBytes - key.size) 0) ++
        (msg.data.toList ++ List.replicate ((P.blockBytes - msg.size % P.blockBytes) %
          P.blockBytes) 0)
      if pre = [] then List.replicate P.blockBytes 0 else pre := by
  have hs : ∀ b : ByteArray, (b.size = 0) = (b.data.toList = []) := by
    intro b
    rw [← List.length_eq_zero_iff, Array.length_toList, ByteArray.size_data]
  simp only [Fast.pad]
  generalize hq : (if key.size = 0 then ByteArray.empty else
      key ++ ByteArray.zeros (P.blockBytes - key.size)) ++ msg ++
      ByteArray.zeros ((P.blockBytes - msg.size % P.blockBytes) % P.blockBytes) = q
  have hpre : q.data.toList =
      (if key.size = 0 then [] else
          key.data.toList ++ List.replicate (P.blockBytes - key.size) 0) ++
        (msg.data.toList ++ List.replicate ((P.blockBytes - msg.size % P.blockBytes) %
          P.blockBytes) 0) := by
    subst hq
    split <;> simp [ByteArray.zeros]
  rw [← hpre]
  by_cases h : q.size = 0 <;> have h' := h <;> rw [hs] at h' <;>
    simp only [h, h', ↓reduceIte, ByteArray.zeros, Array.toList_replicate]

theorem blocks_eq (hP : P.Valid) (key msg : ByteArray) (hkey : key.size ≤ P.blockBytes) :
    Reference.blocks P key.data.toList msg.data.toList =
      chunks P.blockBytes (Fast.pad P key msg).data.toList := by
  obtain ⟨_, hk, _, _, _, _, hbb, _⟩ := hP
  have hb : 0 < P.blockBytes := by omega
  rw [data_pad, Reference.blocks]
  simp only [Array.length_toList, ByteArray.size_data]
  generalize msg.data.toList ++ List.replicate ((P.blockBytes - msg.size % P.blockBytes) %
    P.blockBytes) 0 = L
  have hpre : chunks P.blockBytes ((if key.size = 0 then [] else
      key.data.toList ++ List.replicate (P.blockBytes - key.size) 0) ++ L) =
      (if key.size = 0 then [] else
        [key.data.toList ++ List.replicate (P.blockBytes - key.size) 0]) ++
      chunks P.blockBytes L := by
    split
    · rfl
    · rw [chunks_append _ hb _ _ (by simp; omega), List.singleton_append]
  rw [← hpre]
  generalize (if key.size = 0 then [] else
      key.data.toList ++ List.replicate (P.blockBytes - key.size) 0) ++ L = pre
  by_cases h : pre = []
  · subst h
    simp only [chunks_nil, ↓reduceIte]
    rw [← List.append_nil (List.replicate _ _), chunks_append _ hb _ _ (by simp), chunks_nil,
      List.append_nil]
  · have h' : chunks P.blockBytes pre ≠ [] := by
      rw [chunks_of_ne_nil _ hb _ h]; exact List.cons_ne_nil _ _
    simp only [h, h', ↓reduceIte]

theorem size_pad (hP : P.Valid) (key msg : ByteArray) (hkey : key.size ≤ P.blockBytes) :
    ∃ M, 0 < M ∧ (Fast.pad P key msg).size = M * P.blockBytes := by
  obtain ⟨_, hk, _, _, _, _, hbb, _⟩ := hP
  have hb : 0 < P.blockBytes := by omega
  obtain ⟨M, hM⟩ := exists_pad_eq msg.size P.blockBytes hb
  have hs : ∀ b : ByteArray, b.size = b.data.toList.length := by simp
  rw [hs, data_pad]
  generalize hL : msg.data.toList ++ List.replicate ((P.blockBytes - msg.size % P.blockBytes) %
    P.blockBytes) 0 = L
  have hLlen : L.length = M * P.blockBytes := by
    rw [← hL, List.length_append, List.length_replicate, Array.length_toList,
      ByteArray.size_data, hM]
  generalize hpre : (if key.size = 0 then [] else
      key.data.toList ++ List.replicate (P.blockBytes - key.size) 0) ++ L = pre
  have hprelen :
      pre.length = (if key.size = 0 then 0 else 1) * P.blockBytes + M * P.blockBytes := by
    rw [← hpre, List.length_append, hLlen]
    split
    · simp
    · simp only [List.length_append, List.length_replicate, Array.length_toList,
        ByteArray.size_data]
      omega
  by_cases h : pre = []
  · exact ⟨1, by decide, by simp [h]⟩
  · simp only [h, ↓reduceIte, hprelen, ← Nat.add_mul]
    refine ⟨_, ?_, rfl⟩
    rcases Nat.eq_zero_or_pos ((if key.size = 0 then 0 else 1) + M) with h0 | h0
    · exfalso
      apply h
      rw [← List.length_eq_zero_iff, hprelen, ← Nat.add_mul, h0, Nat.zero_mul]
    · exact h0

theorem hashWith_eq (hP : P.Valid) (key salt personal : ByteArray) (nn : Nat) (msg : ByteArray)
    (hkey : key.size ≤ P.blockBytes) :
    (Fast.hashWith α P key salt personal nn msg).data.toList =
      Reference.hash P key.data.toList salt.data.toList personal.data.toList nn
        msg.data.toList := by
  have hP' := hP
  obtain ⟨_, hk, hR1, hR2, hR3, hR4, hbb, _, _, hsb⟩ := hP'
  have hR : P.R.1 < P.w ∧ P.R.2.1 < P.w ∧ P.R.2.2.1 < P.w ∧ P.R.2.2.2 < P.w :=
    ⟨hR1, hR2, hR3, hR4⟩
  have hb : 0 < P.blockBytes := by omega
  have hpb : (Fast.paramBlock P nn key.size salt personal).size = 8 * (P.w / 8) := by
    simp only [Fast.paramBlock, Reference.paramBlock, ByteArray.size, List.size_toArray,
      List.length_append, List.length_cons, List.length_nil, List.length_replicate,
      List.length_take]
    omega
  simp only [Fast.hashWith, Reference.hash, Array.length_toList, ByteArray.size_data]
  rw [blocks_eq P hP key msg hkey]
  obtain ⟨M, hM0, hM⟩ := size_pad P hP key msg hkey
  have hinit := init_eq (α := α) P hP _ hpb
  simp only [Fast.paramBlock, List.toList_toArray] at hinit
  generalize Fast.pad P key msg = p at hM ⊢
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hs : p.data.toList.length = (M + 1) * P.blockBytes := by simp [hM]
  have hgetD : ∀ i, i < M + 1 → ((List.range (M + 1)).map fun i =>
      (p.data.toList.drop (i * P.blockBytes)).take P.blockBytes).getD i [] =
      (p.data.toList.drop (i * P.blockBytes)).take P.blockBytes := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  have hblock : ∀ i, i < M + 1 → bv P (Fast.block (α := α) P p (i * P.blockBytes)) =
      Reference.wordsLE P ((p.data.toList.drop (i * P.blockBytes)).take P.blockBytes) := by
    intro i hi
    apply block_eq P hP
    have := Nat.mul_le_mul_right P.blockBytes (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at this
    omega
  rw [chunks_eq_range _ (M + 1) hb _ hs, List.length_map, List.length_range, hM,
    Nat.mul_div_cancel _ hb, Nat.add_sub_cancel, data_extract_zero, data_foldl_pushLE P,
    F_eq P hR, hgetD M (by omega), ← hblock M (by omega), ← hinit]
  have hfold := foldl_hom_of_mem (bv (α := α) P)
    (fun h i => Fast.F P P.rounds h (Fast.block P p (i * P.blockBytes))
      ((i + 1) * P.blockBytes) false)
    (fun h i => Reference.F P P.rounds h (Reference.wordsLE P
      (((List.range (M + 1)).map fun i =>
        (p.data.toList.drop (i * P.blockBytes)).take P.blockBytes).getD i []))
      ((i + 1) * P.blockBytes) false)
    (List.range M)
    (((List.range 8).map fun i =>
      xor (ofNat (P.IV.getD i 0))
        (loadLE (Fast.paramBlock P nn key.size salt personal) (i * (P.w / 8)))).toArray)
    (by
      intro x i hi
      rw [List.mem_range] at hi
      rw [F_eq P hR, hgetD i (by omega), hblock i (by omega)])
  rw [show ByteArray.empty.data.toList = ([] : List UInt8) from rfl, List.nil_append, ← hfold]
  rfl

end Equiv

/-! ### BLAKE2b, BLAKE2s and the EIP-152 compression function -/

/-- BLAKE2b computes the reference for every key of at most one block. -/
theorem blake2bWith_eq (key salt personal : ByteArray) (nn : Nat) (m : ByteArray)
    (hkey : key.size ≤ 128) :
    (blake2bWith key salt personal nn m).data.toList =
      Reference.hash blake2bParams key.data.toList salt.data.toList personal.data.toList nn
        m.data.toList :=
  @Equiv.hashWith_eq UInt64 _ blake2bParams (inferInstanceAs (LawfulWord UInt64 64))
    blake2bParams_valid key salt personal nn m hkey

/-- BLAKE2s computes the reference for every key of at most one block. -/
theorem blake2sWith_eq (key salt personal : ByteArray) (nn : Nat) (m : ByteArray)
    (hkey : key.size ≤ 64) :
    (blake2sWith key salt personal nn m).data.toList =
      Reference.hash blake2sParams key.data.toList salt.data.toList personal.data.toList nn
        m.data.toList :=
  @Equiv.hashWith_eq UInt32 _ blake2sParams (inferInstanceAs (LawfulWord UInt32 32))
    blake2sParams_valid key salt personal nn m hkey

theorem blake2b_eq (m : ByteArray) :
    (blake2b m).data.toList = Reference.hash blake2bParams [] [] [] 64 m.data.toList :=
  blake2bWith_eq _ _ _ _ m (by decide)

theorem blake2s_eq (m : ByteArray) :
    (blake2s m).data.toList = Reference.hash blake2sParams [] [] [] 32 m.data.toList :=
  blake2sWith_eq _ _ _ _ m (by decide)

/-- The BLAKE2b compression function of EIP-152 is the reference `F` for any number of rounds,
with the 128-bit offset counter `t = t₀ + 2⁶⁴ t₁`. -/
theorem blake2bF_eq (rounds : Nat) (h m : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (blake2bF rounds h m t0 t1 f).toList.map UInt64.toBitVec =
      Reference.F blake2bParams rounds (h.toList.map UInt64.toBitVec)
        (m.toList.map UInt64.toBitVec) (t0.toNat + 2 ^ 64 * t1.toNat) f :=
  @Equiv.F_eq UInt64 _ blake2bParams (inferInstanceAs (LawfulWord UInt64 64))
    ⟨by decide, by decide, by decide, by decide⟩ rounds h m _ f

end Hash.BLAKE2
