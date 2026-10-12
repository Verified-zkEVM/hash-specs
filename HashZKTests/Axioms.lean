/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

import HashTests.Audit
import HashZK

/-!
# Axiom audit of the Layer 2 theorems

The theorems relating the fast instances on CompPoly's field representations to the
specifications. The build fails if any of them depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- Poseidon: circomlib's instances over CompPoly's BN254 compute the specification.
audit_axioms HashZK.Poseidon.Circom.permutation_eq HashZK.Poseidon.Circom.poseidon_eq

-- The raw limbs of the C exports preserve the operations, and compute circomlib's Poseidon.
audit_axioms HashZK.Raw.BN254.hom_toRaw HashZK.Raw.BN254.toNat_toRaw
  HashZK.Raw.Poseidon.poseidonNat_eq
