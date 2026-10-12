/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

/-!
# The BLAKE3 binary tree

BLAKE3 splits its input into chunks, the leaves of a binary tree, and combines them with parent
nodes [BLAKE3, §2.1]. The tree is fixed by two rules: left subtrees are complete binary trees
with a power of 2 leaves, and are at least as big as their right siblings. So a tree with
`n ≥ 2` leaves has `2^⌊log₂(n − 1)⌋` leaves on the left.

This file defines the tree generically, for any leaf type `α`, node type `γ` and chaining-value
type `β`, given:

* `leaf i x`: the node for leaf `x` at index `i`;
* `parent l r`: the node for the chaining values `l` and `r` of two children;
* `cv o`: the chaining value of a node.

`root xs off` is the root node of the tree over the leaves `xs`, whose first leaf has index
`off`. It returns a node, not a chaining value, because BLAKE3 treats the root specially.

It also defines the incremental algorithm of [BLAKE3, §5.1.2]: a stack of chaining values of
complete subtrees, merged as leaves arrive (`addLeaf`), and folded into the root at the end
(`finish`). `Hash.Tree.finish_pushAll` in `Hash.Construction.TreeLemmas` proves that the two
compute the same root.

## References

* [BLAKE3] J. O'Connor, J-P. Aumasson, S. Neves, Z. Wilcox-O'Hearn, *BLAKE3: one function, fast
  everywhere*, 2020. <https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf>
-/

@[expose] public section

namespace Hash.Tree

variable {α β γ : Type} [Inhabited α]
variable (leaf : Nat → α → γ) (parent : β → β → γ) (cv : γ → β)

/-- The number of leaves in the left subtree of a tree with `n ≥ 2` leaves: the largest power of
2 less than `n` [BLAKE3, §2.1]. -/
def leftLeaves (n : Nat) : Nat := 2 ^ Nat.log2 (n - 1)

/-- `root` with an explicit fuel argument, so that it reduces in the kernel. -/
def rootAux : Nat → List α → Nat → γ
  | 0, xs, off => leaf off (xs.headD default)
  | fuel + 1, xs, off =>
    if xs.length ≤ 1 then leaf off (xs.headD default) else
      let p := leftLeaves xs.length
      parent (cv (rootAux fuel (xs.take p) off)) (cv (rootAux fuel (xs.drop p) (off + p)))

/-- The root node of the tree over the leaves `xs` (at least one), whose first leaf has index
`off` [BLAKE3, §2.1]. -/
def root (xs : List α) (off : Nat) : γ := rootAux leaf parent cv xs.length xs off

/-- Merge the chaining value `c` of a new complete subtree into the stack (newest first): while
the new total number of leaves, `total`, is even, pop the top entry and merge it with `c` as its
left sibling [BLAKE3, §5.1.2, Listing 1]. -/
def merge : List β → β → Nat → List β
  | [], c, _ => [c]
  | s :: st, c, total =>
    if total % 2 = 0 then merge st (cv (parent s c)) (total / 2) else c :: s :: st

/-- Add leaf `x` with index `i` to the stack. -/
def addLeaf (stack : List β) (i : Nat) (x : α) : List β :=
  merge parent cv stack (cv (leaf i x)) (i + 1)

/-- Add the leaves `xs` to the stack, the first with index `i`. -/
def pushAll : List β → Nat → List α → List β
  | stack, _, [] => stack
  | stack, i, x :: xs => pushAll (addLeaf leaf parent cv stack i x) (i + 1) xs

/-- Merge the node `o` of the last leaf with every entry of the stack, newest first, giving the
root node [BLAKE3, §5.1.2]. -/
def finish (stack : List β) (o : γ) : γ :=
  stack.foldl (fun o s => parent s (cv o)) o

end Hash.Tree
