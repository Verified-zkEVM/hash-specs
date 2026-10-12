/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.BN254
public import HashZK.Poseidon.Circom
public import HashZK.Raw.BN254
public import HashZK.Raw.Equiv
public import HashZK.Raw.Poseidon

/-!
# Layer 2: CompPoly integration

The fast instances of the ZK-friendly hashes on CompPoly's Montgomery field types, with proofs,
through CompPoly's ring isomorphisms, that they compute the specifications over `ZMod p`
(ROADMAP.md Phase 4).

`HashZK.Raw` runs the same computations on CompPoly's raw limbs, without Mathlib in its import
closure, for the C exports of `HashFFI`; `HashZK.Raw.Equiv` proves that it computes the
specifications too.
-/
