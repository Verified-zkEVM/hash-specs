/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Init
public import Hash.BLAKE3.API
public import Hash.Construction.TreeLemmas

/-!
# BLAKE3: streaming equals one-shot

The main result, `Hash.BLAKE3.Fast.State.finalize_updates`, says that feeding any list of pieces
to the streaming interface gives the same output as hashing their concatenation at once, for
every key, mode and output length. The byte-level APIs follow: `Hash.blake3Init_eq`,
`Hash.blake3KeyedInit_eq` and `Hash.blake3DeriveKeyInit_eq`.

The proof has two parts. The streaming state buffers bytes so that the chunks it has added to
the stack, followed by the current chunk, are exactly the chunks of the input so far
(`Inv`). And adding chunks to the stack one at a time computes the same tree as the one-shot
function, by `Hash.Tree.finish_pushAll`.
-/

public section

namespace Hash.BLAKE3.Fast

/-! ### Byte arrays and lists -/

theorem _root_.ByteArray.ext_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) :
    a = b := by
  cases a; cases b
  simp only [ByteArray.mk.injEq]
  exact Array.ext' h

theorem data_extract (b : ByteArray) (i j : Nat) :
    (b.extract i j).data.toList = (b.data.toList.drop i).take (j - i) := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract]

theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := by simp

/-- Consecutive pieces of `c` elements, then the rest, make up the whole list. -/
theorem flatten_pieces {α : Type} (c n : Nat) (l : List α) :
    ((List.range n).map fun j => (l.drop (j * c)).take c).flatten ++ l.drop (n * c) = l := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.append_assoc]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    rw [show (n + 1) * c = n * c + c by rw [Nat.succ_mul], ← List.drop_drop,
      List.take_append_drop, ih]

/-- Piece `j` of a concatenation of pieces of length `c`. -/
theorem piece_flatten {α : Type} (c : Nat) (Q : List (List α)) (r : List α)
    (hQ : ∀ q ∈ Q, q.length = c) (j : Nat) (hj : j < Q.length) :
    ((Q.flatten ++ r).drop (j * c)).take c = Q[j] := by
  induction Q generalizing j with
  | nil => simp at hj
  | cons q Q ih =>
    have hq := hQ q (by simp)
    cases j with
    | zero =>
      simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons, List.append_assoc,
        List.getElem_cons_zero]
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    | succ j =>
      simp only [List.flatten_cons, List.append_assoc, List.getElem_cons_succ]
      rw [Nat.succ_mul, Nat.add_comm, ← List.drop_drop, List.drop_left' hq]
      exact ih (fun q hq' => hQ q (by simp [hq'])) j (by simpa using hj)

theorem length_flatten_of_eq {α : Type} (c : Nat) (Q : List (List α))
    (hQ : ∀ q ∈ Q, q.length = c) : Q.flatten.length = Q.length * c := by
  induction Q with
  | nil => simp
  | cons q Q ih =>
    rw [List.flatten_cons, List.length_append, hQ q (by simp),
      ih (fun q hq => hQ q (by simp [hq])), List.length_cons, Nat.succ_mul, Nat.add_comm]

/-! ### The chunks of the input -/

/-- The input is split into the full chunks `P` and the last chunk `b`. -/
theorem inputChunks_eq (input : ByteArray) (P : List ByteArray) (b : ByteArray)
    (hP : ∀ c ∈ P, c.size = CHUNK_LEN) (hb : b.size ≤ CHUNK_LEN) (hne : P ≠ [] → 0 < b.size)
    (h : (P.map (·.data.toList)).flatten ++ b.data.toList = input.data.toList) :
    inputChunks input = P ++ [b] := by
  have hQ : ∀ q ∈ P.map (·.data.toList), q.length = CHUNK_LEN := by
    intro q hq
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hq
    rw [← size_eq_length]; exact hP c hc
  have hlen : input.size = P.length * CHUNK_LEN + b.size := by
    rw [size_eq_length input, ← h, List.length_append, length_flatten_of_eq _ _ hQ,
      List.length_map, ← size_eq_length]
  have hn : (if input.size = 0 then 1 else (input.size + CHUNK_LEN - 1) / CHUNK_LEN) =
      P.length + 1 := by
    split
    · rename_i h0
      have : P = [] := by
        by_contra hP'
        have := hne hP'
        simp only [CHUNK_LEN] at hlen
        omega
      simp [this]
    · simp only [CHUNK_LEN] at hlen ⊢
      rcases Nat.eq_zero_or_pos b.size with hb0 | hb0
      · have := hne
        by_cases hP0 : P = []
        · simp [hP0] at hlen; omega
        · have := hne hP0; omega
      · simp only [CHUNK_LEN] at hb
        omega
  unfold inputChunks
  simp only []
  rw [hn]
  apply List.ext_getElem
  · simp
  · intro j h1 _
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range]
    apply ByteArray.ext_toList
    rw [data_extract, show (j + 1) * CHUNK_LEN - j * CHUNK_LEN = CHUNK_LEN by
      rw [Nat.succ_mul]; omega, ← h]
    by_cases hj : j < P.length
    · rw [List.getElem_append_left (by simpa using hj),
        piece_flatten CHUNK_LEN _ _ hQ j (by simpa using hj), List.getElem_map]
    · have hj' : j = P.length := by omega
      subst hj'
      rw [List.getElem_append_right (by simp), List.getElem_singleton]
      · rw [show P.length * CHUNK_LEN = ((P.map (·.data.toList)).flatten).length by
          rw [length_flatten_of_eq _ _ hQ, List.length_map], List.drop_left,
          List.take_of_length_le (by rw [← size_eq_length]; exact hb)]

/-! ### The streaming invariant -/

variable (key : Array UInt32) (flags : Nat)

/-- The streaming state `s` has consumed `input`: the chunks `P` added to its stack and its
buffer make up `input`, every added chunk is full, and the buffer holds at most one chunk, and
at least one byte once a chunk has been added. -/
def Inv (s : State) (input : ByteArray) : Prop :=
  s.key = key ∧ s.flags = flags ∧
  ∃ P : List ByteArray,
    s.stack = Tree.pushAll (chunkOutput key flags) (parentOutput key flags)
      Output.chainingValue [] 0 P ∧
    s.count = P.length ∧ (∀ c ∈ P, c.size = CHUNK_LEN) ∧ s.buf.size ≤ CHUNK_LEN ∧
    (P ≠ [] → 0 < s.buf.size) ∧
    (P.map (·.data.toList)).flatten ++ s.buf.data.toList = input.data.toList

theorem inv_init : Inv key flags (State.init key flags) ByteArray.empty :=
  ⟨rfl, rfl, [], rfl, rfl, by simp, by simp [State.init], by simp, by simp [State.init]⟩

theorem pushAll_append {α β γ : Type} [Inhabited α] (leaf : Nat → α → γ)
    (parent : β → β → γ) (cv : γ → β) (st : List β) (i : Nat) (P Q : List α) :
    Tree.pushAll leaf parent cv st i (P ++ Q) =
      Tree.pushAll leaf parent cv (Tree.pushAll leaf parent cv st i P) (i + P.length) Q := by
  induction P generalizing st i with
  | nil => simp [Tree.pushAll]
  | cons x P ih =>
    simp only [List.cons_append, Tree.pushAll, ih, List.length_cons]
    rw [Nat.add_assoc, Nat.add_comm 1]

theorem inv_update (s : State) (input m : ByteArray) (h : Inv key flags s input) :
    Inv key flags (s.update m) (input ++ m) := by
  obtain ⟨hkey, hflags, P, hst, hcount, hP, hbuf, hne, hdata⟩ := h
  have hpl : (s.buf ++ m).data.toList = s.buf.data.toList ++ m.data.toList := by simp
  have hps : (s.buf ++ m).size = s.buf.size + m.size := by simp
  have hfull : ∀ c ∈ State.fullChunks (s.buf ++ m), c.size = CHUNK_LEN := by
    intro c hc
    simp only [State.fullChunks, List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    rw [ByteArray.size_extract]
    simp only [CHUNK_LEN] at hj ⊢
    omega
  have hlenfull : (State.fullChunks (s.buf ++ m)).length =
      ((s.buf ++ m).size - 1) / CHUNK_LEN := by
    simp [State.fullChunks]
  refine ⟨hkey, hflags, P ++ State.fullChunks (s.buf ++ m), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.update]
    rw [pushAll_append, ← hst, Nat.zero_add, ← hcount, hkey, hflags]
  · simp only [State.update, List.length_append, hcount, hlenfull]
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hP c hc
    · exact hfull c hc
  · simp only [State.update, ByteArray.size_extract, Nat.min_self, CHUNK_LEN]
    omega
  · intro hne'
    simp only [State.update, ByteArray.size_extract, Nat.min_self, CHUNK_LEN]
    by_cases hp0 : (s.buf ++ m).size = 0
    · exfalso
      have hPn : P = [] := by
        by_contra hP'
        have := hne hP'
        omega
      have hfn : State.fullChunks (s.buf ++ m) = [] := by
        simp [State.fullChunks, hp0]
      exact hne' (by rw [hPn, hfn]; rfl)
    · omega
  · simp only [State.update, List.map_append, List.flatten_append, List.append_assoc,
      ByteArray.data_append, Array.toList_append, ← hdata]
    congr 1
    have hfc : ((State.fullChunks (s.buf ++ m)).map (·.data.toList)) =
        (List.range (((s.buf ++ m).size - 1) / CHUNK_LEN)).map fun j =>
          ((s.buf ++ m).data.toList.drop (j * CHUNK_LEN)).take CHUNK_LEN := by
      simp only [State.fullChunks, List.map_map]
      apply List.map_congr_left
      intro j _
      simp only [Function.comp, data_extract]
      rw [show (j + 1) * CHUNK_LEN - j * CHUNK_LEN = CHUNK_LEN by rw [Nat.succ_mul]; omega]
    rw [hfc, data_extract, List.take_of_length_le (by simp), flatten_pieces, hpl]

theorem inv_updates (ms : List ByteArray) (s : State) (input : ByteArray)
    (h : Inv key flags s input) :
    Inv key flags (ms.foldl State.update s) (ms.foldl (· ++ ·) input) := by
  induction ms generalizing s input with
  | nil => exact h
  | cons m ms ih => exact ih _ _ (inv_update key flags s input m h)

theorem rootOutput_of_inv (s : State) (input : ByteArray) (h : Inv key flags s input) :
    s.rootOutput = rootOutput key flags input := by
  obtain ⟨hkey, hflags, P, hst, hcount, hP, hbuf, hne, hdata⟩ := h
  rw [rootOutput, inputChunks_eq input P s.buf hP hbuf hne hdata, State.rootOutput, hst,
    hcount, hkey, hflags]
  have := Tree.finish_pushAll (chunkOutput key flags) (parentOutput key flags)
    Output.chainingValue (P ++ [s.buf]) (by simp)
  simp only [List.dropLast_concat, List.length_append, List.length_singleton,
    Nat.add_sub_cancel, List.getLast_concat] at this
  exact this

/-- **Streaming equals one-shot.** Feeding the pieces `ms` to the streaming interface, then
finalizing with output length `d`, gives BLAKE3 of their concatenation. -/
theorem State.finalize_updates (ms : List ByteArray) (d : Nat) :
    (ms.foldl State.update (State.init key flags)).finalize d =
      hashWith key flags (ms.foldl (· ++ ·) ByteArray.empty) d := by
  rw [State.finalize, hashWith,
    rootOutput_of_inv key flags _ _ (inv_updates key flags ms _ _ (inv_init key flags))]

end Hash.BLAKE3.Fast

namespace Hash

open BLAKE3.Fast

theorem blake3Init_eq (ms : List ByteArray) (d : Nat) :
    (ms.foldl State.update blake3Init).finalize d =
      blake3Xof (ms.foldl (· ++ ·) ByteArray.empty) d :=
  State.finalize_updates _ _ ms d

theorem blake3KeyedInit_eq (key : ByteArray) (ms : List ByteArray) (d : Nat) :
    (ms.foldl State.update (blake3KeyedInit key)).finalize d =
      blake3Keyed key (ms.foldl (· ++ ·) ByteArray.empty) d :=
  State.finalize_updates _ _ ms d

theorem blake3DeriveKeyInit_eq (context : ByteArray) (ms : List ByteArray) (d : Nat) :
    (ms.foldl State.update (blake3DeriveKeyInit context)).finalize d =
      blake3DeriveKey context (ms.foldl (· ++ ·) ByteArray.empty) d :=
  State.finalize_updates _ _ ms d

end Hash
