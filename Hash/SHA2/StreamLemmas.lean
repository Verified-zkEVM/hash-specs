/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.SHA2.Equiv
public import Hash.SHA2.Stream

/-!
# SHA-2: streaming equals one-shot

The main result, `Hash.SHA2.Fast.State.finalize_updates`, says that feeding any list of pieces
to the streaming interface gives the same digest as hashing their concatenation at once, for
every member of the family. The byte-level APIs follow: `Hash.sha256Init_eq` and so on.

The streaming state has compressed the first `c` whole blocks of the message so far, and buffers
the remaining bytes, fewer than one block (`Inv`). The one-shot padding of the message is those
`c` blocks followed by the padding of the buffer that `State.finalize` compresses.

The only property of machine words used is that a block's compression depends only on its bytes
(`compress_congr`).
-/

public section

namespace Hash.SHA2.Fast

open Word

variable {α : Type} [Word α] (P : Params) [LawfulWord α P.w]

/-! ### Compression depends only on the block's bytes -/

theorem blockBytes_eq (hw : P.w = 32 ∨ P.w = 64) : P.blockBits / 8 = 16 * (P.w / 8) := by
  rcases hw with h | h <;> simp only [Params.blockBits, h]

theorem loadBE_congr (p q : ByteArray) (a b : Nat) (hp : a + P.w / 8 ≤ p.size)
    (hq : b + P.w / 8 ≤ q.size)
    (h : (p.data.toList.drop a).take (P.w / 8) = (q.data.toList.drop b).take (P.w / 8)) :
    loadBE (α := α) p a = loadBE q b :=
  LawfulWord.toBV_injective (by
    rw [LawfulWord.toBV_loadBE _ _ hp, LawfulWord.toBV_loadBE _ _ hq, h])

theorem compress_congr (K H : Array α) (p q : ByteArray) (a b : Nat)
    (hp : a + P.blockBits / 8 ≤ p.size) (hq : b + P.blockBits / 8 ≤ q.size)
    (h : (p.data.toList.drop a).take (P.blockBits / 8) =
      (q.data.toList.drop b).take (P.blockBits / 8)) :
    compress P K H p a = compress P K H q b := by
  have hbb := blockBytes_eq P (@LawfulWord.w_cases α _ P.w _)
  have hW : schedule (α := α) P p a = schedule P q b := by
    unfold schedule
    apply foldl_congr_mem
    intro W t _
    congr 1
    split
    · rename_i ht
      have ht' : t * (P.w / 8) + P.w / 8 ≤ P.blockBits / 8 := by
        rw [hbb, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ht
      apply loadBE_congr P p q _ _ (by omega) (by omega)
      have key : ∀ l : List UInt8 , ∀ o : Nat,
          ((l.drop o).take (P.blockBits / 8) |>.drop (t * (P.w / 8)) |>.take (P.w / 8)) =
            (l.drop (o + t * (P.w / 8))).take (P.w / 8) := by
        intro l o
        rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
      rw [← key, ← key, h]
    · rfl
  unfold compress
  rw [hW]

/-- Compressing at an offset inside `p` ignores what follows `p`. -/
theorem compress_prefix (K H : Array α) (p q : ByteArray) (rest : List UInt8)
    (hq : q.data.toList = p.data.toList ++ rest) (a : Nat) (hp : a + P.blockBits / 8 ≤ p.size) :
    compress P K H q a = compress P K H p a := by
  have hql : q.size = p.size + rest.length := by
    rw [size_eq_length, hq, List.length_append, ← size_eq_length]
  apply compress_congr P K H q p a a (by omega) hp
  rw [hq, List.drop_append_of_le_length (by rw [← size_eq_length]; omega),
    List.take_append_of_le_length (by rw [List.length_drop, ← size_eq_length]; omega)]

/-- Compressing at an offset after a prefix `pre` of `q` is compressing in the rest of `q`. -/
theorem compress_shift (K H : Array α) (q t : ByteArray) (pre : List UInt8)
    (hq : q.data.toList = pre ++ t.data.toList) (o : Nat) (ht : o + P.blockBits / 8 ≤ t.size) :
    compress P K H q (pre.length + o) = compress P K H t o := by
  have hql : q.size = pre.length + t.size := by
    rw [size_eq_length, hq, List.length_append, ← size_eq_length]
  apply compress_congr P K H q t _ o (by omega) ht
  rw [hq, ← List.drop_drop, List.drop_left]

/-! ### The invariant -/

/-- Compress block `i` of the message `M`. -/
def cstep (K : Array α) (M : ByteArray) (H : Array α) (i : Nat) : Array α :=
  compress P K H M (i * (P.blockBits / 8))

/-- The first `c` blocks of `M` do not change when more bytes follow. -/
theorem foldl_cstep_prefix (K H : Array α) (M q : ByteArray) (rest : List UInt8)
    (hq : q.data.toList = M.data.toList ++ rest) (c : Nat)
    (hc : c * (P.blockBits / 8) ≤ M.size) :
    (List.range c).foldl (cstep P K q) H = (List.range c).foldl (cstep P K M) H := by
  apply foldl_congr_mem
  intro H i hi
  rw [List.mem_range] at hi
  have : (i + 1) * (P.blockBits / 8) ≤ c * (P.blockBits / 8) := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at this
  exact compress_prefix P K H M q rest hq _ (by omega)

/-- The streaming state `s` has absorbed the message `M`: it has compressed the first `c` blocks
of `M`, and buffers the remaining bytes, fewer than one block. -/
def Inv (M : ByteArray) (s : State α) : Prop :=
  s.P = P ∧ s.K = (P.K.map ofNat).toArray ∧ s.len = M.size ∧ s.buf.size < P.blockBits / 8 ∧
    ∃ c, M.size = c * (P.blockBits / 8) + s.buf.size ∧
      s.buf.data.toList = M.data.toList.drop (c * (P.blockBits / 8)) ∧
      s.H = (List.range c).foldl (cstep P (P.K.map ofNat).toArray M) (P.H0.map ofNat).toArray

theorem inv_init : Inv P ByteArray.empty (State.init α P) := by
  have hbb := blockBytes_eq P (@LawfulWord.w_cases α _ P.w _)
  refine ⟨rfl, rfl, rfl, ?_, 0, by simp [State.init], by simp [State.init], rfl⟩
  change 0 < _
  rcases @LawfulWord.w_cases α _ P.w _ with h | h <;> rw [hbb, h] <;> decide

theorem inv_update (M m : ByteArray) (s : State α) (hs : Inv P M s) :
    Inv P (M ++ m) (s.update m) := by
  obtain ⟨hsP, hsK, hlen, hbl, c, hMs, hbuf, hH⟩ := hs
  have hbb := blockBytes_eq P (@LawfulWord.w_cases α _ P.w _)
  have hb : 0 < P.blockBits / 8 := by
    rcases @LawfulWord.w_cases α _ P.w _ with h | h <;> rw [hbb, h] <;> decide
  have hMm : (M ++ m).data.toList = M.data.toList ++ m.data.toList := by
    rw [ByteArray.data_append, Array.toList_append]
  have hMl : M.data.toList = M.data.toList.take (c * (P.blockBits / 8)) ++ s.buf.data.toList := by
    rw [hbuf, List.take_append_drop]
  have hpre : (M.data.toList.take (c * (P.blockBits / 8))).length = c * (P.blockBits / 8) := by
    rw [List.length_take, ← size_eq_length]; omega
  unfold State.update
  dsimp only
  rw [hsP]
  split
  · rename_i hlt
    refine ⟨rfl, hsK, ?_, ?_, c, ?_, ?_, ?_⟩
    · change s.len + m.size = _; rw [hlen, ByteArray.size_append]
    · change (s.buf ++ m).size < _; rw [ByteArray.size_append]; omega
    · change _ = _ + (s.buf ++ m).size; rw [ByteArray.size_append, ByteArray.size_append]; omega
    · change (s.buf ++ m).data.toList = _
      rw [ByteArray.data_append, Array.toList_append, hbuf, hMm,
        List.drop_append_of_le_length (by rw [← size_eq_length]; omega)]
    · change s.H = _
      rw [foldl_cstep_prefix P _ _ M (M ++ m) _ hMm c (by omega)]; exact hH
  · rename_i hge
    generalize hnd : (P.blockBits / 8 - s.buf.size) % (P.blockBits / 8) = need
    -- Completing the buffered block, if any, compresses the first `c1` blocks of `M ++ m`.
    obtain ⟨c1, hc1, hH1, hneed⟩ : ∃ c1, c1 * (P.blockBits / 8) = M.size + need ∧
        (if s.buf.size = 0 then s.H else compress P s.K s.H (s.buf ++ m.extract 0 need) 0) =
          (List.range c1).foldl (cstep P (P.K.map ofNat).toArray (M ++ m))
            (P.H0.map ofNat).toArray ∧ need ≤ m.size := by
      by_cases hr : s.buf.size = 0
      · have h0 : need = 0 := by rw [← hnd, hr, Nat.sub_zero, Nat.mod_self]
        refine ⟨c, by omega, ?_, by omega⟩
        simp only [hr, ↓reduceIte]
        rw [foldl_cstep_prefix P _ _ M (M ++ m) _ hMm c (by omega)]; exact hH
      · have h1 : need = P.blockBits / 8 - s.buf.size := by
          rw [← hnd]; exact Nat.mod_eq_of_lt (by omega)
        refine ⟨c + 1, by rw [Nat.succ_mul]; omega, ?_, by omega⟩
        simp only [hr, ↓reduceIte]
        rw [List.range_succ, List.foldl_append, foldl_cstep_prefix P _ _ M (M ++ m) _ hMm c
          (by omega), ← hH, List.foldl_cons, List.foldl_nil, hsK]
        simp only [cstep]
        rw [show c * (P.blockBits / 8) = (M.data.toList.take (c * (P.blockBits / 8))).length + 0
          by rw [hpre, Nat.add_zero], compress_shift P _ _ (M ++ m) (s.buf ++ m) _
            (by rw [hMm, ByteArray.data_append, Array.toList_append, ← List.append_assoc, ← hMl])
            0 (by rw [ByteArray.size_append]; omega)]
        symm
        apply compress_prefix P _ _ (s.buf ++ m.extract 0 need) (s.buf ++ m)
          (m.data.toList.drop need)
        · rw [ByteArray.data_append, Array.toList_append, ByteArray.data_append,
            Array.toList_append,
            data_extract, Nat.sub_zero, List.drop_zero, List.append_assoc, List.take_append_drop]
        · rw [ByteArray.size_append, ByteArray.size_extract, Nat.min_eq_left (by omega)]
          omega
    generalize hn : (m.size - need) / (P.blockBits / 8) = n
    have hdm := Nat.div_add_mod (m.size - need) (P.blockBits / 8)
    have hml := Nat.mod_lt (m.size - need) hb
    rw [hn, Nat.mul_comm] at hdm
    have hMs' : M.size = M.data.toList.length := size_eq_length M
    refine ⟨rfl, hsK, ?_, ?_, c1 + n, ?_, ?_, ?_⟩
    · change s.len + m.size = _; rw [hlen, ByteArray.size_append]
    · change (m.extract _ _).size < _
      rw [ByteArray.size_extract, Nat.min_self]; omega
    · change _ = _ + (m.extract _ _).size
      rw [ByteArray.size_append, ByteArray.size_extract, Nat.min_self, Nat.add_mul]; omega
    · change (m.extract _ _).data.toList = _
      have hd : (M.data.toList ++ m.data.toList).drop ((c1 + n) * (P.blockBits / 8)) =
          m.data.toList.drop (need + n * (P.blockBits / 8)) := by
        rw [List.drop_append, List.drop_eq_nil_of_le (by rw [Nat.add_mul]; omega), List.nil_append]
        congr 1
        rw [Nat.add_mul]; omega
      rw [data_extract, List.take_of_length_le (by rw [List.length_drop, ← size_eq_length]),
        hMm, hd]
    · change State.compressBlocks P s.K _ m need n = _
      unfold State.compressBlocks
      rw [hH1, List.range_add, List.foldl_append, List.foldl_map]
      apply foldl_congr_mem
      intro H i hi
      rw [List.mem_range] at hi
      have hi' : (i + 1) * (P.blockBits / 8) ≤ n * (P.blockBits / 8) := Nat.mul_le_mul_right _ hi
      rw [Nat.succ_mul] at hi'
      rw [hsK]
      simp only [cstep]
      rw [show (c1 + i) * (P.blockBits / 8) = M.data.toList.length + (need + i * (P.blockBits / 8))
        by rw [Nat.add_mul]; omega, compress_shift P _ _ (M ++ m) m _ hMm _ (by omega)]
theorem finalize_of_inv (M : ByteArray) (s : State α) (hs : Inv P M s) :
    s.finalize = hashWith α P M := by
  obtain ⟨hsP, hsK, hlen, hbl, c, hMs, hbuf, hH⟩ := hs
  unfold State.finalize hashWith
  dsimp only
  rw [hsP, hsK, hlen]
  have hw := @LawfulWord.w_cases α _ P.w _
  have hbb := blockBytes_eq P hw
  have hb : 0 < P.blockBits / 8 := by rcases hw with h | h <;> rw [hbb, h] <;> decide
  have hMl : M.data.toList = M.data.toList.take (c * (P.blockBits / 8)) ++ s.buf.data.toList := by
    rw [hbuf, List.take_append_drop]
  have hpre : (M.data.toList.take (c * (P.blockBits / 8))).length = c * (P.blockBits / 8) := by
    rw [List.length_take, ← size_eq_length]; omega
  -- The padding: the message, then the bytes `R`; the streaming tail is the buffer, then `R`.
  have hps := Equiv.size_pad P hw M
  generalize hZ : ByteArray.zeros ((P.blockBits / 8 - (M.size + 1 + P.lengthBits / 8) %
    (P.blockBits / 8)) % (P.blockBits / 8)) = Z
  generalize hL : natToBytesBE (P.lengthBits / 8) (8 * M.size) = L
  have hpush : ∀ b : ByteArray, (b.push 128 ++ Z ++ L).data.toList =
      b.data.toList ++ (128 :: (Z.data.toList ++ L.data.toList)) := by
    intro b; simp [ByteArray.data_append, ByteArray.data_push]
  have hpl : (pad P M).data.toList =
      M.data.toList ++ (128 :: (Z.data.toList ++ L.data.toList)) := by
    rw [← hpush, ← hZ, ← hL]; rfl
  generalize ht : s.buf.push 128 ++ Z ++ L = tail
  have hpt : (pad P M).data.toList = M.data.toList.take (c * (P.blockBits / 8)) ++
      tail.data.toList := by
    rw [hpl, ← ht, hpush, ← List.append_assoc, ← hMl]
  -- The tail is whole blocks: `T` of them.
  have hsz : (pad P M).size = c * (P.blockBits / 8) + tail.size := by
    rw [size_eq_length, hpt, List.length_append, hpre, ← size_eq_length]
  rw [hsz, Nat.add_comm, Nat.add_mul_mod_self_right] at hps
  obtain ⟨T, hT⟩ := Nat.dvd_of_mod_eq_zero hps
  have hdiv : (pad P M).size / (P.blockBits / 8) = c + T := by
    rw [hsz, hT, Nat.mul_comm (P.blockBits / 8) T, ← Nat.add_mul, Nat.mul_div_cancel _ hb]
  have htd : tail.size / (P.blockBits / 8) = T := by
    rw [hT, Nat.mul_div_cancel_left _ hb]
  rw [hdiv, htd, List.range_add, List.foldl_append,
    show (fun H i => compress P (List.map ofNat P.K).toArray H (pad P M) (i * (P.blockBits / 8))) =
      cstep (α := α) P (List.map ofNat P.K).toArray (pad P M) from rfl,
    foldl_cstep_prefix P _ _ M (pad P M) _ hpl c (by omega), ← hH, List.foldl_map]
  unfold State.compressBlocks
  rw [foldl_congr_mem _ (fun x y => cstep P (List.map ofNat P.K).toArray (pad P M) x (c + y)) _ _
    fun H i hi => ?_]
  rw [List.mem_range] at hi
  have hi' : (i + 1) * (P.blockBits / 8) ≤ T * (P.blockBits / 8) := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at hi'
  simp only [cstep]
  rw [show (c + i) * (P.blockBits / 8) =
      (M.data.toList.take (c * (P.blockBits / 8))).length + (0 + i * (P.blockBits / 8)) by
    rw [hpre, Nat.add_mul]; omega,
    compress_shift P _ _ (pad P M) tail _ hpt _
      (by rw [hT, Nat.mul_comm (P.blockBits / 8) T]; omega)]

/-- **Streaming equals one-shot.** Feeding the pieces `ms` to the streaming interface, then
finalizing, gives the SHA-2 digest of their concatenation. -/
theorem State.finalize_updates (ms : List ByteArray) :
    (ms.foldl State.update (State.init α P)).finalize =
      hashWith α P (ms.foldl (· ++ ·) ByteArray.empty) := by
  apply finalize_of_inv
  have : ∀ (ms : List ByteArray) (M : ByteArray) (s : State α), Inv P M s →
      Inv P (ms.foldl (· ++ ·) M) (ms.foldl State.update s) := by
    intro ms
    induction ms with
    | nil => exact fun _ _ h => h
    | cons m ms ih => exact fun M s h => ih _ _ (inv_update P M m s h)
  exact this ms _ _ (inv_init P)

end Hash.SHA2.Fast

namespace Hash

open SHA2 SHA2.Fast

theorem sha224Init_eq (ms : List ByteArray) :
    (ms.foldl State.update sha224Init).finalize = sha224 (ms.foldl (· ++ ·) ByteArray.empty) :=
  @State.finalize_updates UInt32 _ SHA2.sha224 (inferInstanceAs (LawfulWord UInt32 32)) ms

theorem sha256Init_eq (ms : List ByteArray) :
    (ms.foldl State.update sha256Init).finalize = sha256 (ms.foldl (· ++ ·) ByteArray.empty) :=
  @State.finalize_updates UInt32 _ SHA2.sha256 (inferInstanceAs (LawfulWord UInt32 32)) ms

theorem sha384Init_eq (ms : List ByteArray) :
    (ms.foldl State.update sha384Init).finalize = sha384 (ms.foldl (· ++ ·) ByteArray.empty) :=
  @State.finalize_updates UInt64 _ SHA2.sha384 (inferInstanceAs (LawfulWord UInt64 64)) ms

theorem sha512Init_eq (ms : List ByteArray) :
    (ms.foldl State.update sha512Init).finalize = sha512 (ms.foldl (· ++ ·) ByteArray.empty) :=
  @State.finalize_updates UInt64 _ SHA2.sha512 (inferInstanceAs (LawfulWord UInt64 64)) ms

theorem sha512t224Init_eq (ms : List ByteArray) :
    (ms.foldl State.update sha512t224Init).finalize =
      sha512t224 (ms.foldl (· ++ ·) ByteArray.empty) :=
  @State.finalize_updates UInt64 _ SHA2.sha512t224 (inferInstanceAs (LawfulWord UInt64 64)) ms

theorem sha512t256Init_eq (ms : List ByteArray) :
    (ms.foldl State.update sha512t256Init).finalize =
      sha512t256 (ms.foldl (· ++ ·) ByteArray.empty) :=
  @State.finalize_updates UInt64 _ SHA2.sha512t256 (inferInstanceAs (LawfulWord UInt64 64)) ms

end Hash
