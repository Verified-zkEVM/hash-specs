/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

/-!
# The Merkle–Damgård construction

A Merkle–Damgård hash function pads its input to a whole number of blocks, then iterates a
compression function over the blocks, starting from a fixed initial value, and outputs a function
of the final chaining value [Merkle 1989, Damgård 1989]. SHA-2 is the instance in this library
[FIPS 180-4, §6].

This file defines the iteration and states its basic properties, which are shared by every
Merkle–Damgård hash.

## References

* [FIPS 180-4] NIST, *Secure Hash Standard (SHS)*, FIPS PUB 180-4, 2015.
  <https://doi.org/10.6028/NIST.FIPS.180-4>
* R. C. Merkle, *One Way Hash Functions and DES*, CRYPTO 1989.
  <https://doi.org/10.1007/0-387-34805-0_40>
* I. B. Damgård, *A Design Principle for Hash Functions*, CRYPTO 1989.
  <https://doi.org/10.1007/0-387-34805-0_39>
-/

@[expose] public section

namespace Hash.MerkleDamgard

variable {σ β : Type}

/-- Iterate the compression function `f` over `blocks`, starting from the chaining value `iv`. -/
def iterate (f : σ → β → σ) (iv : σ) (blocks : List β) : σ :=
  blocks.foldl f iv

@[simp] theorem iterate_nil (f : σ → β → σ) (iv : σ) : iterate f iv [] = iv := rfl

@[simp] theorem iterate_cons (f : σ → β → σ) (iv : σ) (b : β) (bs : List β) :
    iterate f iv (b :: bs) = iterate f (f iv b) bs := rfl

/-- Iteration can be resumed: hashing `xs ++ ys` is hashing `ys` from the chaining value reached
after `xs`. This is what makes streaming implementations possible. -/
theorem iterate_append (f : σ → β → σ) (iv : σ) (xs ys : List β) :
    iterate f iv (xs ++ ys) = iterate f (iterate f iv xs) ys :=
  List.foldl_append

end Hash.MerkleDamgard
