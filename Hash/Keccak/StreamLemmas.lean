/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Keccak.Equiv
public import Hash.Keccak.Stream

/-!
# Keccak: streaming equals one-shot

The main result, `Hash.Keccak.Fast.State.squeezeBytes_updates`, says that feeding any list of
pieces to the streaming interface, then squeezing `d` bytes, gives the sponge of their
concatenation, for every positive rate, domain byte and output length. The byte-level APIs follow:
`Hash.sha3x256Init_eq`, `Hash.shake128Init_eq` and so on.

The streaming state has absorbed the first `c` whole blocks of the message so far, and buffers
the remaining bytes, fewer than one block (`Inv`). The padding depends only on the message length
modulo the rate, so the one-shot padded message is those `c` blocks followed by the padded buffer,
which is exactly one block.

The only property used of the lanes is that absorbing a block depends only on its bytes
(`absorbBlock_congr`).
-/

public section

namespace Hash.Keccak.Fast

/-! ### Absorbing depends only on the block's bytes -/

theorem getUInt64LE_congr (p q : ByteArray) (a b : Nat) (hp : a + 8 ≤ p.size)
    (hq : b + 8 ≤ q.size) (h : (p.data.toList.drop a).take 8 = (q.data.toList.drop b).take 8) :
    ByteArray.getUInt64LE p a = ByteArray.getUInt64LE q b :=
  UInt64.toBitVec_inj.mp (by
    rw [ByteArray.toBitVec_getUInt64LE _ _ hp, ByteArray.toBitVec_getUInt64LE _ _ hq, h])

theorem absorbBlock_congr (rate : Nat) (a : Array UInt64) (p q : ByteArray) (o o' : Nat)
    (hp : o + rate ≤ p.size) (hq : o' + rate ≤ q.size)
    (h : (p.data.toList.drop o).take rate = (q.data.toList.drop o').take rate) :
    absorbBlock rate a p o = absorbBlock rate a q o' := by
  unfold absorbBlock tabulate
  congr 3
  funext i
  split
  · rename_i hi
    have hi' : 8 * i + 8 ≤ rate := by omega
    rw [getUInt64LE_congr p q (o + 8 * i) (o' + 8 * i) (by omega) (by omega)]
    have key : ∀ (l : List UInt8) (o : Nat),
        ((l.drop o).take rate |>.drop (8 * i) |>.take 8) = (l.drop (o + 8 * i)).take 8 := by
      intro l o
      rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
    rw [← key, ← key, h]
  · rfl

/-- Absorbing at an offset inside `p` ignores what follows `p`. -/
theorem absorbBlock_prefix (rate : Nat) (a : Array UInt64) (p q : ByteArray) (rest : List UInt8)
    (hq : q.data.toList = p.data.toList ++ rest) (o : Nat) (hp : o + rate ≤ p.size) :
    absorbBlock rate a q o = absorbBlock rate a p o := by
  have hql : q.size = p.size + rest.length := by
    rw [size_eq_length, hq, List.length_append, ← size_eq_length]
  apply absorbBlock_congr rate a q p o o (by omega) hp
  rw [hq, List.drop_append_of_le_length (by rw [← size_eq_length]; omega),
    List.take_append_of_le_length (by rw [List.length_drop, ← size_eq_length]; omega)]

/-- Absorbing at an offset after a prefix `pre` of `q` is absorbing in the rest of `q`. -/
theorem absorbBlock_shift (rate : Nat) (a : Array UInt64) (q t : ByteArray) (pre : List UInt8)
    (hq : q.data.toList = pre ++ t.data.toList) (o : Nat) (ht : o + rate ≤ t.size) :
    absorbBlock rate a q (pre.length + o) = absorbBlock rate a t o := by
  have hql : q.size = pre.length + t.size := by
    rw [size_eq_length, hq, List.length_append, ← size_eq_length]
  apply absorbBlock_congr rate a q t _ o (by omega) ht
  rw [hq, ← List.drop_drop, List.drop_left]

/-! ### Padding -/

/-- The bytes `pad` appends when `q` bytes are missing from a whole block. -/
def padSuffix (ds : UInt8) (q : Nat) : List UInt8 :=
  if q = 1 then [ds ||| 0x80] else ds :: (List.replicate (q - 2) 0 ++ [0x80])

theorem data_pad (rate : Nat) (ds : UInt8) (b : ByteArray) :
    (pad rate ds b).data.toList = b.data.toList ++ padSuffix ds (rate - b.size % rate) := by
  unfold pad padSuffix
  dsimp only
  split <;> simp [ByteArray.data_push, ByteArray.data_append, ByteArray.zeros]

theorem length_padSuffix (ds : UInt8) (q : Nat) (hq : 0 < q) : (padSuffix ds q).length = q := by
  unfold padSuffix; split <;> simp <;> omega

/-! ### The invariant -/

/-- Absorb block `i` of the message `M`. -/
def astep (rate : Nat) (M : ByteArray) (a : Array UInt64) (i : Nat) : Array UInt64 :=
  absorbBlock rate a M (i * rate)

/-- The first `c` blocks of `M` do not change when more bytes follow. -/
theorem foldl_astep_prefix (rate : Nat) (a : Array UInt64) (M q : ByteArray) (rest : List UInt8)
    (hq : q.data.toList = M.data.toList ++ rest) (c : Nat) (hc : c * rate ≤ M.size) :
    (List.range c).foldl (astep rate q) a = (List.range c).foldl (astep rate M) a := by
  apply foldl_congr_mem
  intro a i hi
  rw [List.mem_range] at hi
  have : (i + 1) * rate ≤ c * rate := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at this
  exact absorbBlock_prefix rate a M q rest hq _ (by omega)

/-- The streaming state `s` has absorbed the message `M`: it has absorbed the first `c` blocks
of `M`, and buffers the remaining bytes, fewer than one block. -/
def Inv (M : ByteArray) (s : State) : Prop :=
  0 < s.rate ∧ s.buf.size < s.rate ∧ ∃ c, M.size = c * s.rate + s.buf.size ∧
    s.buf.data.toList = M.data.toList.drop (c * s.rate) ∧
    s.lanes = (List.range c).foldl (astep s.rate M) (Array.replicate 25 0)

theorem inv_init (rate : Nat) (ds : UInt8) (outLen : Nat) (h : 0 < rate) :
    Inv ByteArray.empty (State.init rate ds outLen) :=
  ⟨h, h, 0, by simp [State.init], by simp [State.init], rfl⟩

theorem update_fields (s : State) (m : ByteArray) :
    (s.update m).rate = s.rate ∧ (s.update m).ds = s.ds ∧ (s.update m).outLen = s.outLen := by
  unfold State.update; split <;> exact ⟨rfl, rfl, rfl⟩

theorem inv_update (M m : ByteArray) (s : State) (hs : Inv M s) : Inv (M ++ m) (s.update m) := by
  obtain ⟨hb, hbl, c, hMs, hbuf, hl⟩ := hs
  have hMm : (M ++ m).data.toList = M.data.toList ++ m.data.toList := by
    rw [ByteArray.data_append, Array.toList_append]
  have hMl : M.data.toList = M.data.toList.take (c * s.rate) ++ s.buf.data.toList := by
    rw [hbuf, List.take_append_drop]
  have hpre : (M.data.toList.take (c * s.rate)).length = c * s.rate := by
    rw [List.length_take, ← size_eq_length]; omega
  unfold State.update
  split
  · rename_i hlt
    refine ⟨hb, ?_, c, ?_, ?_, ?_⟩
    · change (s.buf ++ m).size < s.rate; rw [ByteArray.size_append]; omega
    · change _ = c * s.rate + (s.buf ++ m).size
      rw [ByteArray.size_append, ByteArray.size_append]; omega
    · change (s.buf ++ m).data.toList = (M ++ m).data.toList.drop (c * s.rate)
      rw [ByteArray.data_append, Array.toList_append, hbuf, hMm,
        List.drop_append_of_le_length (by rw [← size_eq_length]; omega)]
    · change s.lanes = (List.range c).foldl (astep s.rate (M ++ m)) _
      rw [foldl_astep_prefix s.rate _ M (M ++ m) _ hMm c (by omega)]; exact hl
  · rename_i hge
    dsimp only
    generalize hnd : (s.rate - s.buf.size) % s.rate = need
    -- Completing the buffered block, if any, absorbs the first `c1` blocks of `M ++ m`.
    obtain ⟨c1, hc1, hl1, hneed⟩ : ∃ c1, c1 * s.rate = M.size + need ∧
        (if s.buf.size = 0 then s.lanes
          else absorbBlock s.rate s.lanes (s.buf ++ m.extract 0 need) 0) =
          (List.range c1).foldl (astep s.rate (M ++ m)) (Array.replicate 25 0) ∧
        need ≤ m.size := by
      by_cases hr : s.buf.size = 0
      · have h0 : need = 0 := by rw [← hnd, hr, Nat.sub_zero, Nat.mod_self]
        refine ⟨c, by omega, ?_, by omega⟩
        simp only [hr, ↓reduceIte]
        rw [foldl_astep_prefix s.rate _ M (M ++ m) _ hMm c (by omega)]; exact hl
      · have h1 : need = s.rate - s.buf.size := by
          rw [← hnd]; exact Nat.mod_eq_of_lt (by omega)
        refine ⟨c + 1, by rw [Nat.succ_mul]; omega, ?_, by omega⟩
        simp only [hr, ↓reduceIte]
        rw [List.range_succ, List.foldl_append, foldl_astep_prefix s.rate _ M (M ++ m) _ hMm c
          (by omega), ← hl, List.foldl_cons, List.foldl_nil]
        simp only [astep]
        rw [show c * s.rate = (M.data.toList.take (c * s.rate)).length + 0 by
            rw [hpre, Nat.add_zero],
          absorbBlock_shift s.rate _ (M ++ m) (s.buf ++ m) _
            (by rw [hMm, ByteArray.data_append, Array.toList_append, ← List.append_assoc, ← hMl])
            0 (by rw [ByteArray.size_append]; omega)]
        symm
        apply absorbBlock_prefix s.rate _ (s.buf ++ m.extract 0 need) (s.buf ++ m)
          (m.data.toList.drop need)
        · rw [ByteArray.data_append, Array.toList_append, ByteArray.data_append,
            Array.toList_append, data_extract, Nat.sub_zero, List.drop_zero, List.append_assoc,
            List.take_append_drop]
        · rw [ByteArray.size_append, ByteArray.size_extract, Nat.min_eq_left (by omega)]
          omega
    generalize hn : (m.size - need) / s.rate = n
    have hdm := Nat.div_add_mod (m.size - need) s.rate
    have hml := Nat.mod_lt (m.size - need) hb
    rw [hn, Nat.mul_comm] at hdm
    refine ⟨hb, ?_, c1 + n, ?_, ?_, ?_⟩
    · change (m.extract _ _).size < s.rate
      rw [ByteArray.size_extract, Nat.min_self]; omega
    · change _ = _ * s.rate + (m.extract _ _).size
      rw [ByteArray.size_append, ByteArray.size_extract, Nat.min_self, Nat.add_mul]; omega
    · change (m.extract _ _).data.toList = _
      have hd : (M.data.toList ++ m.data.toList).drop ((c1 + n) * s.rate) =
          m.data.toList.drop (need + n * s.rate) := by
        rw [List.drop_append, List.drop_eq_nil_of_le
          (by rw [← size_eq_length, Nat.add_mul]; omega), List.nil_append]
        congr 1
        rw [← size_eq_length, Nat.add_mul]; omega
      rw [data_extract, List.take_of_length_le (by rw [List.length_drop, ← size_eq_length]),
        hMm, hd]
    · change State.absorbBlocks s.rate _ m need n = _
      unfold State.absorbBlocks
      rw [hl1, List.range_add, List.foldl_append, List.foldl_map]
      apply foldl_congr_mem
      intro a i hi
      rw [List.mem_range] at hi
      have hi' : (i + 1) * s.rate ≤ n * s.rate := Nat.mul_le_mul_right _ hi
      rw [Nat.succ_mul] at hi'
      simp only [astep]
      rw [show (c1 + i) * s.rate = M.data.toList.length + (need + i * s.rate)
        by rw [← size_eq_length, Nat.add_mul]; omega,
        absorbBlock_shift s.rate _ (M ++ m) m _ hMm _ (by omega)]

theorem squeezeBytes_of_inv (M : ByteArray) (s : State) (hs : Inv M s) (d : Nat) :
    s.squeezeBytes d = sponge s.rate s.ds M d := by
  obtain ⟨hb, hbl, c, hMs, hbuf, hl⟩ := hs
  unfold State.squeezeBytes sponge
  dsimp only
  have hMl : M.data.toList = M.data.toList.take (c * s.rate) ++ s.buf.data.toList := by
    rw [hbuf, List.take_append_drop]
  have hpre : (M.data.toList.take (c * s.rate)).length = c * s.rate := by
    rw [List.length_take, ← size_eq_length]; omega
  -- The message and the buffer have the same length modulo the rate, so the same padding.
  have hmod : M.size % s.rate = s.buf.size := by
    rw [hMs, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbl]
  have hbmod : s.buf.size % s.rate = s.buf.size := Nat.mod_eq_of_lt hbl
  have hpl := data_pad s.rate s.ds M
  have htl := data_pad s.rate s.ds s.buf
  rw [hmod] at hpl
  rw [hbmod] at htl
  have hS := length_padSuffix s.ds (s.rate - s.buf.size) (by omega)
  generalize padSuffix s.ds (s.rate - s.buf.size) = S at hpl htl hS
  generalize ht : pad s.rate s.ds s.buf = tail at htl
  have hpt : (pad s.rate s.ds M).data.toList = M.data.toList.take (c * s.rate) ++
      tail.data.toList := by
    rw [hpl, htl, ← List.append_assoc, ← hMl]
  have hts : tail.size = s.rate := by
    rw [size_eq_length, htl, List.length_append, hS, ← size_eq_length]; omega
  have hdiv : (pad s.rate s.ds M).size / s.rate = c + 1 := by
    rw [size_eq_length, hpt, List.length_append, hpre, ← size_eq_length, hts, ← Nat.succ_mul,
      Nat.mul_div_cancel _ hb]
  rw [hdiv, hts, Nat.div_self hb, List.range_succ, List.foldl_append,
    show (fun a i => absorbBlock s.rate a (pad s.rate s.ds M) (i * s.rate)) =
      astep s.rate (pad s.rate s.ds M) from rfl,
    foldl_astep_prefix s.rate _ M (pad s.rate s.ds M) _ hpl c (by omega), ← hl]
  unfold State.absorbBlocks
  simp only [List.range_one, List.foldl_cons, List.foldl_nil, astep, Nat.zero_mul]
  rw [show c * s.rate = (M.data.toList.take (c * s.rate)).length + 0 by rw [hpre, Nat.add_zero],
    absorbBlock_shift s.rate _ (pad s.rate s.ds M) tail _ hpt 0 (by omega)]

theorem fields_updates (ms : List ByteArray) (s : State) :
    (ms.foldl State.update s).rate = s.rate ∧ (ms.foldl State.update s).ds = s.ds ∧
      (ms.foldl State.update s).outLen = s.outLen := by
  induction ms generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons m ms ih =>
    obtain ⟨h1, h2, h3⟩ := ih (s.update m)
    obtain ⟨h1', h2', h3'⟩ := update_fields s m
    exact ⟨h1.trans h1', h2.trans h2', h3.trans h3'⟩

theorem inv_updates (ms : List ByteArray) (M : ByteArray) (s : State) (hs : Inv M s) :
    Inv (ms.foldl (· ++ ·) M) (ms.foldl State.update s) := by
  induction ms generalizing M s with
  | nil => exact hs
  | cons m ms ih => exact ih _ _ (inv_update M m s hs)

/-- **Streaming equals one-shot.** Feeding the pieces `ms` to the streaming interface, then
squeezing `d` bytes, gives the sponge of their concatenation. -/
theorem State.squeezeBytes_updates (rate : Nat) (ds : UInt8) (outLen : Nat) (h : 0 < rate)
    (ms : List ByteArray) (d : Nat) :
    (ms.foldl State.update (State.init rate ds outLen)).squeezeBytes d =
      sponge rate ds (ms.foldl (· ++ ·) ByteArray.empty) d := by
  obtain ⟨h1, h2, _⟩ := fields_updates ms (State.init rate ds outLen)
  rw [squeezeBytes_of_inv _ _ (inv_updates ms _ _ (inv_init rate ds outLen h)) d, h1, h2]
  rfl

/-- `finalize` squeezes the default output length. -/
theorem State.finalize_updates (rate : Nat) (ds : UInt8) (outLen : Nat) (h : 0 < rate)
    (ms : List ByteArray) :
    (ms.foldl State.update (State.init rate ds outLen)).finalize =
      sponge rate ds (ms.foldl (· ++ ·) ByteArray.empty) outLen := by
  obtain ⟨_, _, h3⟩ := fields_updates ms (State.init rate ds outLen)
  rw [State.finalize, h3]
  exact State.squeezeBytes_updates rate ds outLen h ms outLen

end Hash.Keccak.Fast

namespace Hash

open Keccak.Fast

theorem sha3x224Init_eq (ms : List ByteArray) :
    (ms.foldl State.update sha3x224Init).finalize = sha3x224 (ms.foldl (· ++ ·) ByteArray.empty) :=
  State.finalize_updates _ _ _ (by decide) ms

theorem sha3x256Init_eq (ms : List ByteArray) :
    (ms.foldl State.update sha3x256Init).finalize = sha3x256 (ms.foldl (· ++ ·) ByteArray.empty) :=
  State.finalize_updates _ _ _ (by decide) ms

theorem sha3x384Init_eq (ms : List ByteArray) :
    (ms.foldl State.update sha3x384Init).finalize = sha3x384 (ms.foldl (· ++ ·) ByteArray.empty) :=
  State.finalize_updates _ _ _ (by decide) ms

theorem sha3x512Init_eq (ms : List ByteArray) :
    (ms.foldl State.update sha3x512Init).finalize = sha3x512 (ms.foldl (· ++ ·) ByteArray.empty) :=
  State.finalize_updates _ _ _ (by decide) ms

theorem keccak256Init_eq (ms : List ByteArray) :
    (ms.foldl State.update keccak256Init).finalize =
      keccak256 (ms.foldl (· ++ ·) ByteArray.empty) :=
  State.finalize_updates _ _ _ (by decide) ms

theorem shake128Init_eq (ms : List ByteArray) (d : Nat) :
    (ms.foldl State.update shake128Init).squeezeBytes d =
      shake128 (ms.foldl (· ++ ·) ByteArray.empty) d :=
  State.squeezeBytes_updates _ _ _ (by decide) ms d

theorem shake256Init_eq (ms : List ByteArray) (d : Nat) :
    (ms.foldl State.update shake256Init).squeezeBytes d =
      shake256 (ms.foldl (· ++ ·) ByteArray.empty) d :=
  State.squeezeBytes_updates _ _ _ (by decide) ms d

end Hash
