/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.BN254
public import HashZK.Poseidon.Circom

/-!
# Layer 2: CompPoly integration

The fast instances of the ZK-friendly hashes on CompPoly's Montgomery field types, with proofs,
through CompPoly's ring isomorphisms, that they compute the specifications over `ZMod p`
(ROADMAP.md Phase 4).
-/
