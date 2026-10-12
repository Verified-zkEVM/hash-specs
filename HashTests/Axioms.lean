/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

import HashTests.Audit
import Hash

/-!
# Axiom audit of the library's theorems

Every theorem of Layer 1 that a downstream user may rely on is listed here. The build fails if any
of them depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`.
-/

-- SHA-2 constants [FIPS 180-4, §4.2, §5.3].
audit_axioms Hash.SHA2.K256_eq Hash.SHA2.K512_eq Hash.SHA2.initialHash256_eq
  Hash.SHA2.initialHash512_eq Hash.SHA2.initialHash384_eq Hash.SHA2.initialHash224_eq
  Hash.SHA2.initialHash512t224_eq Hash.SHA2.initialHash512t256_eq

-- SHA-2: the fast specification equals the reference [FIPS 180-4].
audit_axioms Hash.SHA2.Equiv.hashWith_eq Hash.SHA2.sha224_eq Hash.SHA2.sha256_eq
  Hash.SHA2.sha384_eq Hash.SHA2.sha512_eq Hash.SHA2.sha512t224_eq Hash.SHA2.sha512t256_eq

-- Keccak constants [FIPS 202, §3.2.2, §3.2.5].
audit_axioms Hash.Keccak.rhoOffsets_eq Hash.Keccak.roundConstants_eq

-- Keccak: strings and states, Algorithm 7, and prefix consistency [FIPS 202, §3, §6.2].
audit_axioms Hash.Keccak.State.ofString_toString Hash.Keccak.State.toString_ofString
  Hash.Keccak.keccakP_eq_algorithm7 Hash.Keccak.Reference.shake128_prefix
  Hash.Keccak.Reference.shake256_prefix

-- Keccak: the fast specification equals the reference [FIPS 202].
audit_axioms Hash.Keccak.Equiv.keccakP_toString Hash.Keccak.Equiv.sponge_eq
  Hash.Keccak.sha3x224_eq Hash.Keccak.sha3x256_eq Hash.Keccak.sha3x384_eq Hash.Keccak.sha3x512_eq
  Hash.Keccak.shake128_eq Hash.Keccak.shake256_eq Hash.Keccak.keccak256_eq
  Hash.Keccak.shake128_prefix Hash.Keccak.shake256_prefix

-- Keccak-p is a permutation [FIPS 202, §3.3].
audit_axioms Hash.Keccak.keccakPState_bijective Hash.Keccak.keccakP_injective
  Hash.Keccak.keccakP_surjective

-- Constructions.
audit_axioms Hash.MerkleDamgard.iterate_append Hash.Sponge.sponge_prefix
