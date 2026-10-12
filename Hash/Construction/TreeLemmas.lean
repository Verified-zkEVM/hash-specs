/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Init
public import Hash.Construction.Tree
public import Mathlib.Tactic.Ring

/-!
# The chaining-value stack computes the tree

The main result, `Hash.Tree.finish_pushAll`, says that adding the leaves one at a time to the
stack of [BLAKE3, §5.1.2] and finishing with the last leaf gives the root of the tree of
[BLAKE3, §2.1]. This is what makes incremental BLAKE3 equal to one-shot BLAKE3.

The proof follows the explanation of [BLAKE3, §5.1.2]. After `k` leaves, the stack holds one
complete subtree for each 1-bit of `k` (`blocks`): reading `k` from its lowest 1-bit `2^v`, the
top entry covers the last `2^v` leaves, and so on. Adding a leaf merges one subtree for each
trailing 1-bit of `k` (`merge_blocks`). Finishing merges the subtrees from the smallest, and each
merge is a node of the tree because each subtree is bigger than everything to its right
(`finish_blocks`).
-/

public section

namespace Hash.Tree

variable {α β γ : Type} [Inhabited α]
variable (leaf : Nat → α → γ) (parent : β → β → γ) (cv : γ → β)

/-! ### Powers of two -/

theorem leftLeaves_eq {n v : Nat} (h1 : 2 ^ v < n) (h2 : n ≤ 2 ^ (v + 1)) :
    leftLeaves n = 2 ^ v := by
  rw [leftLeaves, (Nat.log2_eq_iff (k := v) (by omega)).2 ⟨by omega, by omega⟩]

theorem leftLeaves_pos (n : Nat) : 0 < leftLeaves n := Nat.two_pow_pos _

theorem leftLeaves_lt {n : Nat} (h : 2 ≤ n) : leftLeaves n < n := by
  have := Nat.log2_self_le (n := n - 1) (by omega)
  unfold leftLeaves
  omega

/-- The lowest 1-bit of `k`, as a power of 2 (0 for `k = 0`). -/
def lowbit (k : Nat) : Nat :=
  if k = 0 then 0 else if k % 2 = 1 then 1 else 2 * lowbit (k / 2)
termination_by k
decreasing_by omega

theorem lowbit_zero : lowbit 0 = 0 := by rw [lowbit]; rfl

theorem lowbit_odd {k : Nat} (h : k % 2 = 1) : lowbit k = 1 := by
  rw [lowbit]
  simp only [show (k = 0) = False from eq_false (by omega), h, ↓reduceIte]

theorem lowbit_two_mul (m : Nat) : lowbit (2 * m) = 2 * lowbit m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [lowbit_zero]
  · rw [lowbit]
    simp only [show (2 * m = 0) = False from eq_false (by omega),
      show (2 * m % 2 = 1) = False from eq_false (by omega), ↓reduceIte,
      Nat.mul_div_cancel_left _ (show 0 < 2 by decide)]

theorem lowbit_mul_two_pow (m j : Nat) : lowbit (m * 2 ^ j) = 2 ^ j * lowbit m := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.pow_succ, show m * (2 ^ j * 2) = 2 * (m * 2 ^ j) by
      rw [Nat.mul_comm 2, Nat.mul_assoc], lowbit_two_mul, ih, ← Nat.mul_assoc,
      Nat.mul_comm 2 (2 ^ j)]

/-- Every positive `k` is an odd number times a power of 2. -/
theorem exists_odd_mul (k : Nat) (hk : 0 < k) : ∃ n j, n % 2 = 1 ∧ k = n * 2 ^ j := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases h : k % 2 = 1
    · exact ⟨k, 0, h, by simp⟩
    · obtain ⟨n, j, hn, hk'⟩ := ih (k / 2) (by omega) (by omega)
      refine ⟨n, j + 1, hn, ?_⟩
      rw [Nat.pow_succ, ← Nat.mul_assoc, ← hk']
      omega

theorem lowbit_odd_mul {n : Nat} (hn : n % 2 = 1) (j : Nat) : lowbit (n * 2 ^ j) = 2 ^ j := by
  rw [lowbit_mul_two_pow, lowbit_odd hn, Nat.mul_one]

theorem lowbit_pos {k : Nat} (hk : 0 < k) : 0 < lowbit k := by
  obtain ⟨n, j, hn, rfl⟩ := exists_odd_mul k hk
  rw [lowbit_odd_mul hn]
  exact Nat.two_pow_pos _

theorem lowbit_le (k : Nat) : lowbit k ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [lowbit_zero]
  · obtain ⟨n, j, hn, rfl⟩ := exists_odd_mul k hk
    rw [lowbit_odd_mul hn]
    exact Nat.le_mul_of_pos_left _ (by omega)

/-- Removing the lowest 1-bit leaves a number whose lowest 1-bit is at least twice as big. -/
theorem two_mul_lowbit_le {k : Nat} (h : 0 < k - lowbit k) :
    2 * lowbit k ≤ lowbit (k - lowbit k) := by
  have hk : 0 < k := by omega
  obtain ⟨n, j, hn, rfl⟩ := exists_odd_mul k hk
  rw [lowbit_odd_mul hn] at h ⊢
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at h
    · exact hm
  have he : (2 * m + 1) * 2 ^ j = m * 2 ^ (j + 1) + 2 ^ j := by rw [Nat.pow_succ]; ring
  rw [show (2 * m + 1) * 2 ^ j - 2 ^ j = m * 2 ^ (j + 1) by omega, lowbit_mul_two_pow,
    Nat.pow_succ, Nat.mul_comm (2 ^ j) 2]
  exact Nat.le_mul_of_pos_right _ (lowbit_pos hm)

/-! ### The root -/

theorem rootAux_fuel (f g : Nat) (xs : List α) (off : Nat) (hf : xs.length ≤ f)
    (hg : xs.length ≤ g) :
    rootAux leaf parent cv f xs off = rootAux leaf parent cv g xs off := by
  induction f generalizing g xs off with
  | zero =>
    cases g with
    | zero => rfl
    | succ g => simp [rootAux, show xs.length ≤ 1 by omega]
  | succ f ih =>
    cases g with
    | zero => simp [rootAux, show xs.length ≤ 1 by omega]
    | succ g =>
      simp only [rootAux]
      split
      · rfl
      · rename_i h
        have hp := leftLeaves_lt (n := xs.length) (by omega)
        have hp0 := leftLeaves_pos xs.length
        rw [ih g _ _ (by simp; omega) (by simp; omega), ih g (xs.drop _) _ (by simp; omega)
          (by simp; omega)]

theorem root_of_length_le_one (xs : List α) (off : Nat) (h : xs.length ≤ 1) :
    root leaf parent cv xs off = leaf off (xs.headD default) := by
  unfold root
  cases hl : xs.length with
  | zero => rfl
  | succ n => simp [rootAux, h]

theorem root_singleton (x : α) (off : Nat) : root leaf parent cv [x] off = leaf off x :=
  root_of_length_le_one leaf parent cv [x] off (by simp)

/-- A tree with at least two leaves: the left subtree has `leftLeaves` leaves. -/
theorem root_of_two_le (xs : List α) (off : Nat) (h : 2 ≤ xs.length) :
    root leaf parent cv xs off =
      parent (cv (root leaf parent cv (xs.take (leftLeaves xs.length)) off))
        (cv (root leaf parent cv (xs.drop (leftLeaves xs.length))
          (off + leftLeaves xs.length))) := by
  have hp := leftLeaves_lt h
  have hp0 := leftLeaves_pos xs.length
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 1 := ⟨xs.length - 1, by omega⟩
  unfold root
  nth_rewrite 1 [hn]
  rw [rootAux]
  simp only [show (xs.length ≤ 1) = False from eq_false (by omega), ↓reduceIte]
  rw [rootAux_fuel leaf parent cv n (xs.take (leftLeaves xs.length)).length _ _
      (by simp; omega) (Nat.le_refl _),
    rootAux_fuel leaf parent cv n (xs.drop (leftLeaves xs.length)).length _ _
      (by simp; omega) (Nat.le_refl _)]

/-! ### Segments and blocks -/

/-- The `len` leaves of `xs` from index `i`. -/
def seg (xs : List α) (i len : Nat) : List α := (xs.drop i).take len

omit [Inhabited α] in
theorem length_seg (xs : List α) (i len : Nat) (h : i + len ≤ xs.length) :
    (seg xs i len).length = len := by
  simp [seg]; omega

omit [Inhabited α] in
theorem take_seg (xs : List α) (i p len : Nat) (h : p ≤ len) :
    (seg xs i len).take p = seg xs i p := by
  simp [seg, List.take_take, Nat.min_eq_left h]

omit [Inhabited α] in
theorem drop_seg (xs : List α) (i p len : Nat) :
    (seg xs i (p + len)).drop p = seg xs (i + p) len := by
  simp [seg, List.drop_take, List.drop_drop]

omit [Inhabited α] in
theorem seg_one (xs : List α) (k : Nat) (h : k < xs.length) : seg xs k 1 = [xs[k]] := by
  rw [seg, List.drop_eq_getElem_cons h]
  rfl

/-- Merging two adjacent complete subtrees of `p` leaves gives the subtree of their `2p`
leaves; more generally, a subtree of `p` leaves (a power of 2) followed by `1 ≤ len ≤ p` leaves
is the tree over both. -/
theorem root_seg_add (xs : List α) (i v len : Nat) (h1 : 1 ≤ len) (h2 : len ≤ 2 ^ v)
    (h : i + 2 ^ v + len ≤ xs.length) :
    parent (cv (root leaf parent cv (seg xs i (2 ^ v)) i))
        (cv (root leaf parent cv (seg xs (i + 2 ^ v) len) (i + 2 ^ v))) =
      root leaf parent cv (seg xs i (2 ^ v + len)) i := by
  have hl := length_seg xs i (2 ^ v + len) (by omega)
  have hv := Nat.two_pow_pos v
  have hp : leftLeaves (seg xs i (2 ^ v + len)).length = 2 ^ v := by
    rw [hl]
    exact leftLeaves_eq (by omega) (by rw [Nat.pow_succ]; omega)
  rw [root_of_two_le leaf parent cv (seg xs i (2 ^ v + len)) i (by omega), hp,
    take_seg _ _ _ _ (by omega), drop_seg]

/-- The stack after `k` leaves, newest first: one complete subtree per 1-bit of `k`. -/
def blocks (xs : List α) (k : Nat) : List β :=
  if k = 0 then [] else
    cv (root leaf parent cv (seg xs (k - lowbit k) (lowbit k)) (k - lowbit k)) ::
      blocks xs (k - lowbit k)
termination_by k
decreasing_by have := lowbit_pos (k := k) (by omega); omega

theorem blocks_zero (xs : List α) : blocks leaf parent cv xs 0 = [] := by
  rw [blocks]; rfl

theorem blocks_pos (xs : List α) {k : Nat} (hk : 0 < k) :
    blocks leaf parent cv xs k =
      cv (root leaf parent cv (seg xs (k - lowbit k) (lowbit k)) (k - lowbit k)) ::
        blocks leaf parent cv xs (k - lowbit k) := by
  rw [blocks]
  simp only [show (k = 0) = False from eq_false (by omega), ↓reduceIte]

/-- Adding a complete subtree of `2^j` leaves that ends at leaf `N = n·2^j` to the stack of the
first `N − 2^j` leaves gives the stack of the first `N` leaves. -/
theorem merge_blocks (xs : List α) (n j : Nat) (hn : 0 < n) (h : n * 2 ^ j ≤ xs.length) :
    merge parent cv (blocks leaf parent cv xs (n * 2 ^ j - 2 ^ j))
        (cv (root leaf parent cv (seg xs (n * 2 ^ j - 2 ^ j) (2 ^ j)) (n * 2 ^ j - 2 ^ j)))
        n =
      blocks leaf parent cv xs (n * 2 ^ j) := by
  induction n using Nat.strongRecOn generalizing j with
  | _ n ih =>
    have hj := Nat.two_pow_pos j
    have hN : 2 ^ j ≤ n * 2 ^ j := Nat.le_mul_of_pos_left _ hn
    by_cases hodd : n % 2 = 1
    · -- No merge: push the new subtree.
      rw [blocks_pos leaf parent cv xs (k := n * 2 ^ j) (by omega), lowbit_odd_mul hodd]
      cases hb : blocks leaf parent cv xs (n * 2 ^ j - 2 ^ j) with
      | nil => rfl
      | cons s st => simp [merge, hodd]
    · -- Merge with the top entry, the subtree of the previous `2^j` leaves.
      obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
      have hm : 0 < m := by omega
      have hm2 : m * 2 ^ (j + 1) = 2 * m * 2 ^ j := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, ← Nat.mul_assoc, Nat.mul_comm m 2]
      have hj2 : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
      have hmj : 2 ^ (j + 1) ≤ m * 2 ^ (j + 1) := Nat.le_mul_of_pos_left _ hm
      have hlow : lowbit (2 * m * 2 ^ j - 2 ^ j) = 2 ^ j := by
        rw [show 2 * m * 2 ^ j - 2 ^ j = (2 * m - 1) * 2 ^ j by
          rw [Nat.sub_mul, Nat.one_mul]]
        exact lowbit_odd_mul (by omega) j
      rw [blocks_pos leaf parent cv xs (k := 2 * m * 2 ^ j - 2 ^ j) (by omega), hlow]
      simp only [merge, show 2 * m % 2 = 0 by omega, ↓reduceIte,
        show 2 * m / 2 = m by omega]
      have hseg := root_seg_add leaf parent cv xs (2 * m * 2 ^ j - 2 ^ j - 2 ^ j) j (2 ^ j)
        (by omega) (Nat.le_refl _) (by omega)
      rw [show 2 * m * 2 ^ j - 2 ^ j - 2 ^ j + 2 ^ j = 2 * m * 2 ^ j - 2 ^ j by omega] at hseg
      rw [hseg, show 2 ^ j + 2 ^ j = 2 ^ (j + 1) by omega,
        show 2 * m * 2 ^ j - 2 ^ j - 2 ^ j = m * 2 ^ (j + 1) - 2 ^ (j + 1) by omega,
        ih m (by omega) (j + 1) hm (by omega), hm2]

/-- The stack after the first `k` leaves. -/
theorem pushAll_take (xs : List α) (k : Nat) (hk : k ≤ xs.length) :
    pushAll leaf parent cv [] 0 (xs.take k) = blocks leaf parent cv xs k := by
  induction k with
  | zero => simp [pushAll, blocks_zero]
  | succ k ih =>
    have hpush : ∀ (st : List β) (i : Nat) (ys : List α) (y : α),
        pushAll leaf parent cv st i (ys ++ [y]) =
          addLeaf leaf parent cv (pushAll leaf parent cv st i ys) (i + ys.length) y := by
      intro st i ys y
      induction ys generalizing st i with
      | nil => simp [pushAll]
      | cons z zs ih' =>
        simp only [List.cons_append, pushAll, ih', List.length_cons]
        rw [Nat.add_assoc, Nat.add_comm 1]
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some, hpush,
      ih (by omega), List.length_take, Nat.min_eq_left (by omega), Nat.zero_add, addLeaf]
    have h := merge_blocks leaf parent cv xs (k + 1) 0 (by omega) (by simpa using hk)
    simp only [Nat.pow_zero, Nat.mul_one, Nat.add_sub_cancel] at h
    rw [← h, seg_one xs k (by omega), root_singleton]

/-- Finishing the stack of the first `k` leaves with the tree over the next `len` leaves gives
the tree over all `k + len` leaves, if `1 ≤ len` and `len` is at most the smallest subtree in
the stack. -/
theorem finish_blocks (xs : List α) (k len : Nat) (h1 : 1 ≤ len)
    (h2 : k = 0 ∨ len ≤ lowbit k) (h : k + len ≤ xs.length) :
    finish parent cv (blocks leaf parent cv xs k) (root leaf parent cv (seg xs k len) k) =
      root leaf parent cv (seg xs 0 (k + len)) 0 := by
  induction k using Nat.strongRecOn generalizing len with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [finish, blocks_zero]
    · have hp := lowbit_pos hk
      have hpk := lowbit_le k
      obtain ⟨n, j, hn, hkn⟩ := exists_odd_mul k hk
      have hlow : lowbit k = 2 ^ j := by rw [hkn, lowbit_odd_mul hn]
      have hlen : len ≤ 2 ^ j := by rcases h2 with h2 | h2 <;> omega
      rw [blocks_pos leaf parent cv xs hk, finish, List.foldl_cons, ← finish]
      have hseg := root_seg_add leaf parent cv xs (k - lowbit k) j len h1 hlen (by omega)
      rw [hlow] at hseg ⊢
      rw [show k - 2 ^ j + 2 ^ j = k by omega] at hseg
      rw [hseg, ih (k - 2 ^ j) (by omega) (2 ^ j + len) (by omega) ?_ (by omega),
        show k - 2 ^ j + (2 ^ j + len) = k + len by omega]
      by_cases hz : k - 2 ^ j = 0
      · exact .inl hz
      · right
        have := two_mul_lowbit_le (k := k) (by omega)
        rw [hlow] at this
        omega

/-- **Incremental tree hashing computes the tree.** Adding all leaves but the last to the
chaining-value stack, then finishing with the node of the last leaf, gives the root node of the
tree over all the leaves [BLAKE3, §5.1.2]. -/
theorem finish_pushAll (xs : List α) (hxs : xs ≠ []) :
    finish parent cv (pushAll leaf parent cv [] 0 xs.dropLast)
        (leaf (xs.length - 1) (xs.getLast hxs)) =
      root leaf parent cv xs 0 := by
  have hn : 0 < xs.length := List.length_pos_iff.2 hxs
  rw [List.dropLast_eq_take, pushAll_take leaf parent cv xs _ (by omega)]
  have h := finish_blocks leaf parent cv xs (xs.length - 1) 1 (Nat.le_refl _) ?_ (by omega)
  · have e : seg xs 0 xs.length = xs := by simp [seg]
    rw [show xs.length - 1 + 1 = xs.length by omega, e, seg_one xs _ (by omega),
      root_singleton] at h
    rw [← h, List.getLast_eq_getElem]
  · rcases Nat.eq_zero_or_pos (xs.length - 1) with h0 | h0
    · exact .inl h0
    · exact .inr (lowbit_pos h0)

/-! ### Changing representation -/

/-- `root` commutes with a change of representation of the leaves, nodes and chaining values
that commutes with `leaf`, `parent` and `cv`. -/
theorem root_map {α' β' γ' : Type} [Inhabited α'] (leaf' : Nat → α' → γ')
    (parent' : β' → β' → γ') (cv' : γ' → β') (f : γ → γ') (g : β → β') (h : α → α')
    (hdef : h default = default) (hleaf : ∀ i x, f (leaf i x) = leaf' i (h x))
    (hparent : ∀ a b, f (parent a b) = parent' (g a) (g b)) (hcv : ∀ o, g (cv o) = cv' (f o))
    (xs : List α) (off : Nat) :
    f (root leaf parent cv xs off) = root leaf' parent' cv' (xs.map h) off := by
  unfold root
  rw [List.length_map]
  generalize xs.length = fuel
  induction fuel generalizing xs off with
  | zero =>
    simp only [rootAux, hleaf]
    cases xs <;> simp [hdef]
  | succ fuel ih =>
    simp only [rootAux, List.length_map]
    split
    · rw [hleaf]
      cases xs <;> simp [hdef]
    · rw [hparent, hcv, hcv, ih, ih, List.map_take, List.map_drop]

end Hash.Tree
