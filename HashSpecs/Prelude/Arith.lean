/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

/-!
# Kernel-friendly arithmetic for deriving constants

Several hash standards define their constants as "nothing-up-my-sleeve" numbers, such as the
fractional parts of square or cube roots of primes. To prove that a constant table matches its
definition, we compute the definition in the kernel. The functions here therefore use structural
recursion on an explicit fuel argument rather than well-founded recursion. This file is
Mathlib-free.
-/

@[expose] public section

namespace HashSpecs

/-- Trial-division primality test. -/
def isPrimeB (p : Nat) : Bool :=
  2 ≤ p && (List.range' 2 (p - 2)).all fun d => p < d * d || p % d != 0

/-- The first `n` primes, searching candidates below `bound`. -/
def primesBelow (bound : Nat) : List Nat :=
  (List.range bound).filter isPrimeB

/-- Binary search for `⌊n^(1/k)⌋` on the interval `[lo, hi)`, with `fuel` steps. -/
def irootAux (k n : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if mid ^ k ≤ n then irootAux k n fuel mid hi else irootAux k n fuel lo mid

/-- The integer `k`-th root `⌊n^(1/k)⌋`, for `1 ≤ k`. -/
def iroot (k n : Nat) : Nat :=
  irootAux k n (n.log2 + 2) 0 (n + 1)

/-- The first `w` bits of the fractional part of the `k`-th root of `p`, as a number below `2^w`:
`⌊frac(p^(1/k)) · 2^w⌋ = ⌊(p · 2^(k·w))^(1/k)⌋ mod 2^w`. -/
def fracRootBits (k w p : Nat) : Nat :=
  iroot k (p * 2 ^ (k * w)) % 2 ^ w

end HashSpecs
