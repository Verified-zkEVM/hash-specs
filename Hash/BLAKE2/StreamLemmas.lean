/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.BLAKE2.Equiv
public import Hash.BLAKE2.Stream

/-!
# BLAKE2: streaming equals one-shot

The main result, `Hash.BLAKE2.Fast.State.finalize_updates`, says that feeding any list of pieces
to the streaming interface gives the same output as hashing their concatenation at once, for
every key of at most one block, salt, personalisation and output length. The byte-level APIs
follow: `Hash.blake2bInit_eq` and `Hash.blake2sInit_eq`.

Call the key block, if any, followed by the message so far, the *data*. The streaming state has
compressed the first `c` whole blocks of the data, with the same counters as the one-shot
function, and buffers the remaining one to `bb` bytes; it buffers nothing only before any data
(`Inv`). The one-shot function pads the data with zeros to whole blocks, so its last block is
the buffer zero-padded, compressed with the final flag as `State.finalize` does.

The only property of machine words used is that a block depends only on its bytes
(`block_congr`).
-/

public section

namespace Hash.BLAKE2.Fast

open Word

variable {α : Type} [Word α] (P : Params) [LawfulWord α P.w]

/-! ### Blocks depend only on their bytes -/

theorem block_congr (hP : P.Valid) (p q : ByteArray) (i j : Nat)
    (hp : i + P.blockBytes ≤ p.size) (hq : j + P.blockBytes ≤ q.size)
    (h : (p.data.toList.drop i).take P.blockBytes = (q.data.toList.drop j).take P.blockBytes) :
    block (α := α) P p i = block P q j := by
  have hb := Equiv.block_eq (α := α) P hP p i hp
  rw [h, ← Equiv.block_eq (α := α) P hP q j hq] at hb
  exact Array.ext' ((List.map_inj_right fun _ _ => (LawfulWord.toBV_injective ·)).1 hb)

/-- Compress block `i` of the data `D`, not as the last block. -/
def step (D : ByteArray) (h : Array α) (i : Nat) : Array α :=
  F P P.rounds h (block P D (i * P.blockBytes)) ((i + 1) * P.blockBytes) false

/-- The first `c` blocks of the data do not change when more data follows. -/
theorem foldl_step_append (hP : P.Valid) (D E : ByteArray) (h : Array α) (c : Nat)
    (hc : c * P.blockBytes ≤ D.size) :
    (List.range c).foldl (step P (D ++ E)) h = (List.range c).foldl (step P D) h := by
  apply foldl_congr_mem
  intro h i hi
  rw [List.mem_range] at hi
  have hi' : (i + 1) * P.blockBytes ≤ c * P.blockBytes := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at hi'
  simp only [step]
  rw [block_congr P hP (D ++ E) D (i * P.blockBytes) (i * P.blockBytes)
    (by rw [ByteArray.size_append]; omega) (by omega)]
  rw [ByteArray.data_append, Array.toList_append, List.drop_append_of_le_length
    (by rw [← size_eq_length]; omega), List.take_append_of_le_length
    (by rw [List.length_drop, ← size_eq_length]; omega)]

/-! ### The invariant -/

/-- The streaming state `s` has compressed the first `c` blocks of the data `D` from the initial
chain value `h0`, with the remaining bytes of `D` buffered: between one and `bb` of them, or none
if no block has been compressed. -/
def Inv (h0 : Array α) (D : ByteArray) (s : State α) : Prop :=
  s.P = P ∧ ∃ c, s.count = c * P.blockBytes ∧
    s.buf.data.toList = D.data.toList.drop (c * P.blockBytes) ∧ s.buf.size ≤ P.blockBytes ∧
    (s.buf.size = 0 → c = 0) ∧ s.h = (List.range c).foldl (step P D) h0

theorem inv_update (hP : P.Valid) (h0 : Array α) (D m : ByteArray) (s : State α)
    (hs : Inv P h0 D s) : Inv P h0 (D ++ m) (s.update m) := by
  obtain ⟨hsP, c, hcount, hbuf, hle, h0c, hh⟩ := hs
  have hb := hP.blockBytes_pos
  subst hsP
  -- The data before the buffer is whole blocks.
  have hcD : c * s.P.blockBytes ≤ D.size := by
    by_cases h0 : s.buf.size = 0
    · rw [h0c h0, Nat.zero_mul]; omega
    · have : s.buf.data.toList ≠ [] := by
        rw [← List.length_pos_iff, ← size_eq_length]; omega
      rw [hbuf] at this
      have := List.length_pos_iff.2 this
      rw [List.length_drop, ← size_eq_length] at this
      omega
  have hpl : (s.buf ++ m).data.toList = (D ++ m).data.toList.drop (c * s.P.blockBytes) := by
    rw [ByteArray.data_append, Array.toList_append, hbuf, ByteArray.data_append,
      Array.toList_append, List.drop_append_of_le_length (by rw [← size_eq_length]; omega)]
  have hps : (s.buf ++ m).size = s.buf.size + m.size := ByteArray.size_append
  have hps' : (s.buf ++ m).size = D.size + m.size - c * s.P.blockBytes := by
    rw [size_eq_length, hpl, List.length_drop, ← size_eq_length, ByteArray.size_append]
  have hdm := Nat.div_add_mod ((s.buf ++ m).size - 1) s.P.blockBytes
  have hml := Nat.mod_lt ((s.buf ++ m).size - 1) hb
  have hsz : (State.update s m).buf.size =
      (s.buf ++ m).size - ((s.buf ++ m).size - 1) / s.P.blockBytes * s.P.blockBytes := by
    change (ByteArray.extract _ _ _).size = _
    rw [ByteArray.size_extract, Nat.min_self]
  revert hsz
  generalize hp : s.buf ++ m = p at *
  generalize hn : (p.size - 1) / s.P.blockBytes = n at *
  rw [Nat.mul_comm] at hdm
  intro hsz
  refine ⟨rfl, c + n, ?_, ?_, ?_, ?_, ?_⟩
  · change s.count + ((s.buf ++ m).size - 1) / s.P.blockBytes * s.P.blockBytes = _
    rw [hp, hn, hcount, Nat.add_mul]
  · change (ByteArray.extract (s.buf ++ m) _ _).data.toList = _
    rw [hp, hn, data_extract, hpl, List.drop_drop, Nat.add_mul,
      List.take_of_length_le
        (by rw [List.length_drop, ← size_eq_length, ByteArray.size_append]; omega)]
  · rw [hsz]; omega
  · rw [hsz]
    intro h0
    have hp0 : p.size = 0 := by omega
    have hn0 : n = 0 := by rw [← hn, hp0, Nat.zero_sub, Nat.zero_div]
    rw [hn0, Nat.add_zero]
    exact h0c (by omega)
  · change (List.range (((s.buf ++ m).size - 1) / s.P.blockBytes)).foldl _ s.h = _
    rw [hp, hn, List.range_add, List.foldl_append, foldl_step_append s.P hP D m h0 c hcD, ← hh,
      List.foldl_map]
    apply foldl_congr_mem
    intro h i hi
    rw [List.mem_range] at hi
    have hi' : (i + 1) * s.P.blockBytes ≤ n * s.P.blockBytes := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at hi'
    simp only [step]
    rw [hcount, block_congr s.P hP p (D ++ m) (i * s.P.blockBytes) ((c + i) * s.P.blockBytes)
      (by omega) (by rw [ByteArray.size_append, Nat.add_mul]; omega)]
    · congr 1
      simp only [Nat.add_mul, Nat.one_mul]; omega
    · rw [hpl, List.drop_drop, Nat.add_mul]
theorem inv_updates (hP : P.Valid) (h0 : Array α) (ms : List ByteArray) (D : ByteArray)
    (s : State α) (hs : Inv P h0 D s) :
    Inv P h0 (ms.foldl (· ++ ·) D) (ms.foldl State.update s) := by
  induction ms generalizing D s with
  | nil => exact hs
  | cons m ms ih => exact ih _ _ (inv_update P hP h0 D m s hs)

omit [LawfulWord α P.w] in
theorem inv_init (key salt personal : ByteArray) (nn : Nat)
    (hkey : key.size ≤ P.blockBytes) :
    Inv P (State.init α P key salt personal nn).h (State.init α P key salt personal nn).buf
      (State.init α P key salt personal nn) := by
  refine ⟨rfl, 0, (Nat.zero_mul _).symm, by rw [Nat.zero_mul, List.drop_zero], ?_,
    fun _ => rfl, rfl⟩
  change (if key.size = 0 then ByteArray.empty
    else key ++ ByteArray.zeros (P.blockBytes - key.size)).size ≤ _
  split
  · exact Nat.zero_le _
  · rw [size_eq_length, ByteArray.data_append, Array.toList_append, List.length_append]
    simp [ByteArray.zeros]; omega

theorem nn_updates (ms : List ByteArray) (s : State α) :
    (ms.foldl State.update s).nn = s.nn := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih => exact ih _

theorem finalize_of_inv (hP : P.Valid) (key salt personal : ByteArray) (nn : Nat)
    (hkey : key.size ≤ P.blockBytes) (msg : ByteArray) (s : State α)
    (hs : Inv P (State.init α P key salt personal nn).h
      ((State.init α P key salt personal nn).buf ++ msg) s) (hnn : s.nn = nn) :
    s.finalize = hashWith α P key salt personal nn msg := by
  obtain ⟨hsP, c, hcount, hbuf, hle, h0c, hh⟩ := hs
  have hb := hP.blockBytes_pos
  generalize hK : (State.init α P key salt personal nn).buf = K at hbuf hh
  have hKl : K.data.toList = if key.size = 0 then [] else
      key.data.toList ++ List.replicate (P.blockBytes - key.size) 0 := by
    rw [← hK]
    change (if key.size = 0 then ByteArray.empty
      else key ++ ByteArray.zeros (P.blockBytes - key.size)).data.toList = _
    split <;> simp [ByteArray.zeros]
  have hKs : K.size = if key.size = 0 then 0 else P.blockBytes := by
    rw [size_eq_length, hKl]; split <;> simp; omega
  -- The data `D` is `c` whole blocks, then the `r` buffered bytes.
  generalize hD : K ++ msg = D at hbuf hh
  have hDl : D.data.toList = K.data.toList ++ msg.data.toList := by
    rw [← hD, ByteArray.data_append, Array.toList_append]
  have hDs : D.size = K.size + msg.size := by rw [← hD, ByteArray.size_append]
  have hcD : c * P.blockBytes ≤ D.size := by
    by_cases h0 : s.buf.size = 0
    · rw [h0c h0, Nat.zero_mul]; omega
    · have : s.buf.data.toList ≠ [] := by
        rw [← List.length_pos_iff, ← size_eq_length]; omega
      rw [hbuf] at this
      have := List.length_pos_iff.2 this
      rw [List.length_drop, ← size_eq_length] at this
      omega
  have hr : D.size = c * P.blockBytes + s.buf.size := by
    rw [size_eq_length s.buf, hbuf, List.length_drop, ← size_eq_length]; omega
  -- The one-shot function pads the data with zeros to `c + 1` blocks.
  have hpadl : (pad P key msg).data.toList =
      D.data.toList ++ List.replicate (P.blockBytes - s.buf.size) 0 := by
    obtain ⟨M, hM0, hM⟩ := Equiv.size_pad P hP key msg hkey
    rw [size_eq_length, Equiv.data_pad] at hM
    rw [Equiv.data_pad, hDl, ← hKl]
    dsimp only at hM ⊢
    rw [← hKl] at hM
    split
    · rename_i hpre
      rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at hpre
      have : D.size = 0 := by
        rw [size_eq_length, hDl, hpre.1, hpre.2.1]; rfl
      have hr0 : s.buf.size = 0 := by omega
      rw [hpre.1, hpre.2.1, hr0, Nat.sub_zero]; rfl
    · rename_i hpre
      split at hM
      · contradiction
      -- `D` is not empty: else the padded data would be empty.
      have hDne : D.size ≠ 0 := by
        intro h0
        apply hpre
        have hK0 : K.data.toList = [] := by
          rw [← List.length_eq_zero_iff, ← size_eq_length]; omega
        have hm0 : msg.size = 0 := by omega
        have hm0' : msg.data.toList = [] := by
          rw [← List.length_eq_zero_iff, ← size_eq_length]; omega
        rw [hK0, hm0', hm0, Nat.zero_mod, Nat.sub_zero, Nat.mod_self]; rfl
      have hz := Nat.mod_lt (P.blockBytes - msg.size % P.blockBytes) hb
      generalize (P.blockBytes - msg.size % P.blockBytes) % P.blockBytes = z at hpre hM hz ⊢
      rw [List.length_append, List.length_append, List.length_replicate, ← size_eq_length,
        ← size_eq_length] at hM
      have hr1 : 0 < s.buf.size := by
        rcases Nat.eq_zero_or_pos s.buf.size with h0 | h0
        · have := h0c h0; subst this; omega
        · exact h0
      have h1 : c * P.blockBytes < M * P.blockBytes := by omega
      have h2 : M * P.blockBytes < (c + 2) * P.blockBytes := by
        rw [Nat.add_mul]; omega
      have hMc : M = c + 1 := by
        have := Nat.lt_of_mul_lt_mul_right h1
        have := Nat.lt_of_mul_lt_mul_right h2
        omega
      rw [hMc, Nat.succ_mul] at hM
      rw [List.append_assoc, show z = P.blockBytes - s.buf.size by omega]
  have hpad : pad P key msg = D ++ ByteArray.zeros (P.blockBytes - s.buf.size) :=
    ByteArray.ext_toList (by
      rw [hpadl, ByteArray.data_append, Array.toList_append]; simp [ByteArray.zeros])
  have hdd : (pad P key msg).size / P.blockBytes - 1 = c := by
    rw [size_eq_length, hpadl, List.length_append, List.length_replicate, ← size_eq_length,
      show D.size + (P.blockBytes - s.buf.size) = (c + 1) * P.blockBytes by
        rw [Nat.succ_mul]; omega,
      Nat.mul_div_cancel _ hb, Nat.add_sub_cancel]
  have hblk : block (α := α) P (s.buf ++ ByteArray.zeros (P.blockBytes - s.buf.size)) 0 =
      block P (D ++ ByteArray.zeros (P.blockBytes - s.buf.size)) (c * P.blockBytes) := by
    apply block_congr P hP
    · rw [ByteArray.size_append, size_zeros]; omega
    · rw [ByteArray.size_append, size_zeros]; omega
    · simp only [ByteArray.data_append, Array.toList_append, List.drop_zero]
      rw [List.drop_append_of_le_length (by rw [← size_eq_length]; omega), ← hbuf]
  have hct : s.count + s.buf.size =
      if key.size = 0 then msg.size else msg.size + P.blockBytes := by
    rw [hcount]
    by_cases hk : key.size = 0 <;> simp only [hk, ↓reduceIte] at hKs ⊢ <;> omega
  have hh' : s.h = (List.range c).foldl (step P D) ((List.range 8).map fun i =>
      xor (ofNat (P.IV.getD i 0) : α)
        (loadLE (paramBlock P nn key.size salt personal) (i * (P.w / 8)))).toArray := hh
  rw [State.finalize, hashWith, hsP, hdd,
    show (fun h i => F P P.rounds h (block P (pad P key msg) (i * P.blockBytes))
      ((i + 1) * P.blockBytes) false) = step (α := α) P (pad P key msg) from rfl,
    hpad, foldl_step_append P hP D _ _ c hcD, ← hh', hblk, hct, hnn]

/-- **Streaming equals one-shot.** Feeding the pieces `ms` to the streaming interface, then
finalizing, gives BLAKE2 of their concatenation, for every key of at most one block. -/
theorem State.finalize_updates (hP : P.Valid) (key salt personal : ByteArray) (nn : Nat)
    (hkey : key.size ≤ P.blockBytes) (ms : List ByteArray) :
    (ms.foldl State.update (State.init α P key salt personal nn)).finalize =
      hashWith α P key salt personal nn (ms.foldl (· ++ ·) ByteArray.empty) := by
  apply finalize_of_inv P hP key salt personal nn hkey
  · rw [← foldl_append_bytes]
    exact inv_updates P hP _ ms _ _ (inv_init P key salt personal nn hkey)
  · rw [nn_updates]; rfl

end Hash.BLAKE2.Fast

namespace Hash

open BLAKE2 BLAKE2.Fast

theorem blake2bInit_eq (key salt personal : ByteArray) (nn : Nat) (ms : List ByteArray)
    (hkey : key.size ≤ 128) :
    (ms.foldl State.update (blake2bInit key salt personal nn)).finalize =
      blake2bWith key salt personal nn (ms.foldl (· ++ ·) ByteArray.empty) :=
  @State.finalize_updates UInt64 _ blake2bParams (inferInstanceAs (LawfulWord UInt64 64))
    blake2bParams_valid key salt personal nn hkey ms

theorem blake2sInit_eq (key salt personal : ByteArray) (nn : Nat) (ms : List ByteArray)
    (hkey : key.size ≤ 64) :
    (ms.foldl State.update (blake2sInit key salt personal nn)).finalize =
      blake2sWith key salt personal nn (ms.foldl (· ++ ·) ByteArray.empty) :=
  @State.finalize_updates UInt32 _ blake2sParams (inferInstanceAs (LawfulWord UInt32 32))
    blake2sParams_valid key salt personal nn hkey ms

end Hash
