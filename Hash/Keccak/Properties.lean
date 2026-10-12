/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Construction.SpongeLemmas
public import Hash.Keccak.SHA3
public import Hash.Keccak.StateLemmas

/-!
# Properties of the SHA-3 functions

Prefix consistency of the extendable-output functions SHAKE128 and SHAKE256: a shorter output is
a prefix of a longer one [FIPS 202, §6.2].
-/

public section

namespace Hash.Keccak.Reference

theorem keccak_prefix (c : Nat) (hc : c < 1600) (N : List Bool) {d₁ d₂ : Nat} (h : d₁ ≤ d₂) :
    keccak c N d₁ = (keccak c N d₂).take d₁ :=
  Sponge.sponge_prefix _ _ _ _ (by omega) (by omega)
    (fun S => by rw [length_keccakP 6 24 (by decide)]; rfl) N h

/-- SHAKE128 is prefix-consistent: its first `d₁` output bits do not depend on how many more
are requested. -/
theorem shake128_prefix (M : List Bool) {d₁ d₂ : Nat} (h : d₁ ≤ d₂) :
    shake128 M d₁ = (shake128 M d₂).take d₁ :=
  keccak_prefix 256 (by decide) _ h

/-- SHAKE256 is prefix-consistent: its first `d₁` output bits do not depend on how many more
are requested. -/
theorem shake256_prefix (M : List Bool) {d₁ d₂ : Nat} (h : d₁ ≤ d₂) :
    shake256 M d₁ = (shake256 M d₂).take d₁ :=
  keccak_prefix 512 (by decide) _ h

end Hash.Keccak.Reference
