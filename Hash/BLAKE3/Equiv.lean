/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.BLAKE2.Equiv
public import Hash.BLAKE3.API
public import Hash.BLAKE3.StreamLemmas
public import Hash.Construction.TreeLemmas

/-!
# BLAKE3: the fast specification equals the reference

The main results say that the byte-level BLAKE3 functions of `Hash.BLAKE3.API` (computed by
`Hash.BLAKE3.Fast`) produce exactly the bytes of the reference specification
`Hash.BLAKE3.Reference`, for every input and output length: `Hash.BLAKE3.blake3Xof_eq`,
`Hash.BLAKE3.blake3Keyed_eq` and `Hash.BLAKE3.blake3DeriveKey_eq`.

The proof reuses the BLAKE2s round equivalence of `Hash.BLAKE2.Equiv`, relates the compression
function, the chunk and parent nodes, and the output, and then maps the whole tree with
`Hash.Tree.root_map`.
-/

public section

namespace Hash.BLAKE3.Equiv

open BLAKE2.Fast.Word

/-- An array of words as the list of bit vectors it denotes. -/
abbrev bv (v : Array UInt32) : List Reference.Word := v.toList.map UInt32.toBitVec

instance : BLAKE2.LawfulWord UInt32 BLAKE2.blake2sParams.w :=
  inferInstanceAs (BLAKE2.LawfulWord UInt32 32)

theorem toBitVec_get (v : Array UInt32) (i : Nat) :
    (BLAKE2.Fast.get v i).toBitVec = (bv v).getD i 0 :=
  BLAKE2.Equiv.toBV_get (α := UInt32) BLAKE2.blake2sParams v i

theorem toBitVec_xor (a b : UInt32) : (xor a b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

theorem toBitVec_ofNat (n : Nat) : (ofNat n : UInt32).toBitVec = BitVec.ofNat 32 n := rfl

theorem bv_toArray (l : List UInt32) : bv l.toArray = l.map UInt32.toBitVec := by simp [bv]

theorem bv_append (a b : Array UInt32) : bv (a ++ b) = bv a ++ bv b := by simp [bv]

theorem round_eq (m v : Array UInt32) :
    bv (BLAKE2.Fast.round BLAKE2.blake2sParams m v 0) = Reference.round (bv m) (bv v) :=
  BLAKE2.Equiv.round_eq (α := UInt32) BLAKE2.blake2sParams
    ⟨by decide, by decide, by decide, by decide⟩ m v 0

theorem permute_eq (m : Array UInt32) : bv (Fast.permute m) = Reference.permute (bv m) := by
  simp only [Fast.permute, Reference.permute, bv_toArray, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, toBitVec_get]

theorem compress_eq (h m : Array UInt32) (t b d : Nat) :
    bv (Fast.compress h m t b d) = Reference.compress (bv h) (bv m) t b d := by
  have hfold : ∀ (l : List Nat) (vm : Array UInt32 × Array UInt32),
      (bv (l.foldl (fun (vm : Array UInt32 × Array UInt32) _ =>
            (BLAKE2.Fast.round BLAKE2.blake2sParams vm.2 vm.1 0, Fast.permute vm.2)) vm).1,
        bv (l.foldl (fun (vm : Array UInt32 × Array UInt32) _ =>
            (BLAKE2.Fast.round BLAKE2.blake2sParams vm.2 vm.1 0, Fast.permute vm.2)) vm).2) =
        l.foldl (fun (vm : List Reference.Word × List Reference.Word) _ =>
          (Reference.round vm.2 vm.1, Reference.permute vm.2)) (bv vm.1, bv vm.2) := by
    intro l
    induction l with
    | nil => intro vm; rfl
    | cons i l ih =>
      intro vm
      simp only [List.foldl_cons]
      rw [ih, round_eq, permute_eq]
  simp only [Fast.compress, Reference.compress]
  have := hfold (List.range 7) (h ++ ((IV.take 4).map ofNat).toArray ++
    #[ofNat t, ofNat (t / 2 ^ 32), ofNat b, ofNat d], m)
  have hv : bv (h ++ ((IV.take 4).map ofNat).toArray ++
      #[ofNat t, ofNat (t / 2 ^ 32), ofNat b, ofNat d]) =
      bv h ++ (IV.take 4).map (BitVec.ofNat 32) ++
        [BitVec.ofNat 32 t, BitVec.ofNat 32 (t / 2 ^ 32), BitVec.ofNat 32 b,
          BitVec.ofNat 32 d] := by
    simp [bv, List.map_map, Function.comp_def, toBitVec_ofNat]
  rw [hv] at this
  have h1 := congrArg Prod.fst this
  simp only at h1
  simp only [bv_toArray, List.map_append, List.map_map, Function.comp_def, toBitVec_xor,
    toBitVec_get, h1]

/-! ### Nodes and output -/

/-- A fast node as a reference node. -/
def toRef (o : Fast.Output) : Reference.Output :=
  ⟨bv o.cv, bv o.block, o.counter, o.blockLen, o.flags⟩

theorem bv_extract_zero (a : Array UInt32) (n : Nat) : bv (a.extract 0 n) = (bv a).take n := by
  simp [bv, Array.toList_extract, List.extract, List.map_take]

theorem chainingValue_eq (o : Fast.Output) :
    bv o.chainingValue = (toRef o).chainingValue := by
  rw [Fast.Output.chainingValue, Reference.Output.chainingValue, bv_extract_zero, compress_eq]
  rfl

theorem data_foldl_compress (F : Nat → Array UInt32) (l : List Nat) (a : ByteArray) :
    (l.foldl (fun acc i => (F i).foldl pushLE acc) a).data.toList =
      a.data.toList ++ l.flatMap fun i => Reference.wordsToBytes (bv (F i)) := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, ih, List.flatMap_cons, ← List.append_assoc]
    congr 1
    exact BLAKE2.Equiv.data_foldl_pushLE (α := UInt32) BLAKE2.blake2sParams (F i) a

theorem rootBytes_eq (o : Fast.Output) (d : Nat) :
    (o.rootBytes d).data.toList = (toRef o).rootBytes d := by
  rw [Fast.Output.rootBytes, BLAKE2.Equiv.data_extract_zero, data_foldl_compress]
  simp only [Reference.Output.rootBytes, compress_eq]
  rfl

theorem parentOutput_eq (key : Array UInt32) (flags : Nat) (l r : Array UInt32) :
    toRef (Fast.parentOutput key flags l r) =
      Reference.parentOutput (bv key) flags (bv l) (bv r) := by
  simp [toRef, Fast.parentOutput, Reference.parentOutput, bv_append]

/-! ### Chunks and blocks -/

/-- A slice of a zero-padded list is the zero-padded slice. -/
theorem take_drop_append_zeros (l : List UInt8) (z k c : Nat) (h : k + c ≤ l.length + z) :
    ((l ++ List.replicate z 0).drop k).take c =
      (l.drop k).take c ++ List.replicate (c - ((l.drop k).take c).length) 0 := by
  rw [List.drop_append, List.take_append, List.drop_replicate, List.take_replicate]
  congr 2
  simp only [List.length_drop, List.length_take]
  omega

/-- The blocks of a chunk, as slices. -/
theorem chunkBlocks_eq (l : List UInt8) :
    Reference.chunkBlocks l =
      (List.range (if l.length = 0 then 1 else (l.length + blockLen - 1) / blockLen)).map
        fun j => (l.drop (j * blockLen)).take blockLen := by
  unfold Reference.chunkBlocks
  by_cases h : l = []
  · subst h; rfl
  · have h' : ¬ l.length = 0 := fun h0 => h (List.eq_nil_of_length_eq_zero h0)
    simp only [h, h', ↓reduceIte]
    rw [chunks_eq_map_range _ (by decide)]

/-- The inputs are split into the same chunks. -/
theorem inputChunks_eq (input : ByteArray) :
    (Fast.inputChunks input).map (·.data.toList) = Reference.inputChunks input.data.toList := by
  unfold Fast.inputChunks Reference.inputChunks
  have hs : input.size = input.data.toList.length := by simp
  by_cases h : input.data.toList = []
  · have h' : input.size = 0 := by rw [hs, h]; rfl
    simp only [h, h', ↓reduceIte]
    simp [h]
  · have h' : ¬ input.size = 0 := fun h0 => h (List.eq_nil_of_length_eq_zero (hs ▸ h0))
    simp only [h, h', ↓reduceIte]
    rw [chunks_eq_map_range _ (by decide), hs, List.map_map]
    apply List.map_congr_left
    intro j _
    simp only [Function.comp, data_extract]
    rw [show (j + 1) * chunkLen - j * chunkLen = chunkLen by rw [Nat.succ_mul]; omega]

theorem chunkOutput_eq (key : Array UInt32) (flags i : Nat) (chunk : ByteArray) :
    toRef (Fast.chunkOutput key flags i chunk) =
      Reference.chunkOutput (bv key) flags i chunk.data.toList := by
  have hs : chunk.size = chunk.data.toList.length := by simp
  simp only [Fast.chunkOutput, Reference.chunkOutput, chunkBlocks_eq, ← hs, List.length_map,
    List.length_range]
  generalize hnb : (if chunk.size = 0 then 1 else (chunk.size + blockLen - 1) / blockLen) = nb
  have hnb1 : 1 ≤ nb := by
    rw [← hnb]; split
    · exact Nat.le_refl _
    · simp only [blockLen]; omega
  have hL : chunk.size ≤ nb * blockLen := by
    rw [← hnb]; split
    · simp only [blockLen]; omega
    · simp only [blockLen]; omega
  have hlast : (nb - 1) * blockLen ≤ chunk.size := by
    rw [← hnb]; split
    · simp
    · simp only [blockLen]; omega
  set p := chunk ++ ByteArray.zeros (nb * blockLen - chunk.size) with hp
  have hz : (ByteArray.zeros (nb * blockLen - chunk.size)).size =
      nb * blockLen - chunk.size := by
    simp only [ByteArray.zeros, ByteArray.size, Array.size_replicate]
  have hps : p.size = nb * blockLen := by
    rw [hp, ByteArray.size_append, hz]; omega
  have hpl : p.data.toList =
      chunk.data.toList ++ List.replicate (nb * blockLen - chunk.size) 0 := by
    simp [p, ByteArray.zeros]
  have hgetD : ∀ j, j < nb → ((List.range nb).map fun j =>
      (chunk.data.toList.drop (j * blockLen)).take blockLen).getD j [] =
      (chunk.data.toList.drop (j * blockLen)).take blockLen := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  have hblk : ∀ j, j < nb → bv (BLAKE2.Fast.block BLAKE2.blake2sParams p (j * blockLen)) =
      Reference.wordsLE ((chunk.data.toList.drop (j * blockLen)).take blockLen ++
        List.replicate (blockLen -
          ((chunk.data.toList.drop (j * blockLen)).take blockLen).length) 0) := by
    intro j hj
    have hj' : (j + 1) * blockLen ≤ nb * blockLen := Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at hj'
    have := BLAKE2.Equiv.block_eq (α := UInt32) BLAKE2.blake2sParams
      BLAKE2.blake2sParams_valid p (j * blockLen)
      (by rw [hps]; exact hj')
    refine this.trans ?_
    rw [Reference.wordsLE, hpl]
    congr 1
    exact take_drop_append_zeros _ _ _ blockLen (by rw [← hs]; omega)
  simp only [toRef, Reference.Output.mk.injEq]
  refine ⟨?_, ?_, trivial, ?_, trivial⟩
  · refine (foldl_hom_of_mem bv _ _ _ _ ?_).symm
    intro x j hj
    rw [List.mem_range] at hj
    rw [bv_extract_zero, compress_eq, hblk j (by omega), hgetD j (by omega)]
  · rw [hblk (nb - 1) (by omega), hgetD (nb - 1) (by omega)]
  · rw [hgetD (nb - 1) (by omega), List.length_take, List.length_drop, ← hs]
    simp only [blockLen] at hL hlast ⊢
    omega

/-! ### BLAKE3 -/

theorem default_data : (default : ByteArray).data.toList = [] := rfl

/-- The fast BLAKE3 computes the reference, for every key, mode flags and output length. -/
theorem hashWith_eq (key : Array UInt32) (flags : Nat) (input : ByteArray) (d : Nat) :
    (Fast.hashWith key flags input d).data.toList =
      Reference.hashWith (bv key) flags input.data.toList d := by
  rw [Fast.hashWith, rootBytes_eq, Fast.rootOutput,
    Tree.root_map (Fast.chunkOutput key flags) (Fast.parentOutput key flags)
      Fast.Output.chainingValue (Reference.chunkOutput (bv key) flags)
      (Reference.parentOutput (bv key) flags) Reference.Output.chainingValue toRef bv
      (·.data.toList) default_data (chunkOutput_eq key flags) (parentOutput_eq key flags)
      chainingValue_eq,
    inputChunks_eq, Reference.hashWith]

theorem bv_ivWords : bv Fast.ivWords = IV.map (BitVec.ofNat 32) := by
  simp [Fast.ivWords, bv_toArray, List.map_map, Function.comp_def, toBitVec_ofNat]

theorem bv_keyWords (key : ByteArray) (h : key.size = 32) :
    bv (Fast.keyWords key) = Reference.wordsLE key.data.toList := by
  have hs : key.size = key.data.toList.length := by simp
  rw [Reference.wordsLE, BLAKE2.Equiv.wordsLE_eq BLAKE2.blake2sParams (by decide) _ 8
      (by rw [← hs, h]; rfl), Fast.keyWords, bv_toArray, List.map_map]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  exact BLAKE2.LawfulWord.toBV_loadLE (α := UInt32) (w := 32) key (4 * j)
    (by change 4 * j + 4 ≤ key.size; omega) |>.trans (by rw [Nat.mul_comm 4 j]; rfl)

theorem length_compress (h m : List Reference.Word) (t b d : Nat) :
    (Reference.compress h m t b d).length = 16 := by
  simp [Reference.compress]

theorem length_wordsToBytes (ws : List Reference.Word) :
    (Reference.wordsToBytes ws).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [Reference.wordsToBytes, List.flatMap_cons, List.length_append, ← Reference.wordsToBytes,
      ih, List.length_map, List.length_range, List.length_cons]
    omega

theorem length_rootBytes (o : Reference.Output) (d : Nat) : (o.rootBytes d).length = d := by
  rw [Reference.Output.rootBytes, List.length_take,
    length_flatMap_of_length _ _ 64 (fun i _ => by rw [length_wordsToBytes, length_compress]),
    List.length_range]
  omega

/-- Prefix consistency of the reference output: asking for fewer bytes gives a prefix of the
longer output [BLAKE3, §2.6]. -/
theorem rootBytes_prefix (o : Reference.Output) {d₁ d₂ : Nat} (h : d₁ ≤ d₂) :
    o.rootBytes d₁ = (o.rootBytes d₂).take d₁ := by
  simp only [Reference.Output.rootBytes, List.take_take, Nat.min_eq_left h]
  set F := fun i => Reference.wordsToBytes (Reference.compress o.cv o.block i o.blockLen
    (o.flags ||| Flag.root))
  obtain ⟨k, hk⟩ : ∃ k, (d₂ + 63) / 64 = (d₁ + 63) / 64 + k :=
    ⟨(d₂ + 63) / 64 - (d₁ + 63) / 64, by omega⟩
  have hlen : ((List.range ((d₁ + 63) / 64)).flatMap F).length = (d₁ + 63) / 64 * 64 :=
    by rw [length_flatMap_of_length _ _ 64 (fun i _ => by
      simp only [F]; rw [length_wordsToBytes, length_compress]), List.length_range]
  rw [hk, List.range_add, List.flatMap_append, List.take_append_of_le_length (by omega)]

end Hash.BLAKE3.Equiv

namespace Hash.BLAKE3

/-- BLAKE3 computes the reference `hash` mode, for every input and output length. -/
theorem blake3Xof_eq (m : ByteArray) (d : Nat) :
    (blake3Xof m d).data.toList = Reference.hash m.data.toList d := by
  rw [blake3Xof, Equiv.hashWith_eq, Equiv.bv_ivWords, Reference.hash]

theorem blake3_eq (m : ByteArray) : (blake3 m).data.toList = Reference.hash m.data.toList 32 :=
  blake3Xof_eq m 32

/-- Shorter BLAKE3 outputs are prefixes of longer ones [BLAKE3, §2.6]. -/
theorem blake3Xof_prefix (m : ByteArray) {d₁ d₂ : Nat} (h : d₁ ≤ d₂) :
    (blake3Xof m d₁).data.toList = ((blake3Xof m d₂).data.toList).take d₁ := by
  rw [blake3Xof_eq, blake3Xof_eq, Reference.hash, Reference.hash, Reference.hashWith,
    Reference.hashWith, Equiv.rootBytes_prefix _ h]

/-- BLAKE3 `keyed_hash` computes the reference for every 32-byte key. -/
theorem blake3Keyed_eq (key m : ByteArray) (d : Nat) (h : key.size = 32) :
    (blake3Keyed key m d).data.toList =
      Reference.keyedHash key.data.toList m.data.toList d := by
  rw [blake3Keyed, Equiv.hashWith_eq, Equiv.bv_keyWords key h, Reference.keyedHash]

/-- BLAKE3 `derive_key` computes the reference. -/
theorem blake3DeriveKey_eq (context material : ByteArray) (d : Nat) :
    (blake3DeriveKey context material d).data.toList =
      Reference.deriveKey context.data.toList material.data.toList d := by
  have hc := Equiv.hashWith_eq Fast.ivWords Flag.deriveKeyContext context 32
  have hsize : (Fast.hashWith Fast.ivWords Flag.deriveKeyContext context 32).size = 32 := by
    rw [show ∀ b : ByteArray, b.size = b.data.toList.length by simp, hc, Reference.hashWith,
      Equiv.length_rootBytes]
  rw [blake3DeriveKey, Equiv.hashWith_eq, blake3ContextKey, Equiv.bv_keyWords _ hsize, hc,
    Equiv.bv_ivWords,
    Reference.deriveKey]

end Hash.BLAKE3
