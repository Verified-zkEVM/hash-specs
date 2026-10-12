/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.BLAKE2.Reference
public import Hash.SHA2.Constants

/-!
# BLAKE2 constants

The BLAKE2 initialization vectors are those of SHA-2 [RFC 7693, §2.6]: BLAKE2b uses the SHA-512
initial hash value and BLAKE2s the SHA-256 one, which `Hash.SHA2` derives from the square roots
of the first eight primes.
-/

public section

namespace Hash.BLAKE2

/-- The BLAKE2b IV is the SHA-512 initial hash value. -/
theorem blake2b_IV : blake2bParams.IV = SHA2.initialHash512 := by decide +kernel

/-- The BLAKE2s IV is the SHA-256 initial hash value. -/
theorem blake2s_IV : blake2sParams.IV = SHA2.initialHash256 := by decide +kernel

/-- Each row of `SIGMA` is a permutation of the sixteen message-word indices. -/
theorem SIGMA_perm : SIGMA.length = 10 ∧ ∀ s ∈ SIGMA, s.Perm (List.range 16) := by
  decide +kernel

end Hash.BLAKE2
