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

-- SHA-2: streaming equals one-shot.
audit_axioms Hash.SHA2.Fast.State.finalize_updates Hash.sha224Init_eq Hash.sha256Init_eq
  Hash.sha384Init_eq Hash.sha512Init_eq Hash.sha512t224Init_eq Hash.sha512t256Init_eq

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

-- Keccak: streaming equals one-shot.
audit_axioms Hash.Keccak.Fast.State.squeezeBytes_updates Hash.Keccak.Fast.State.finalize_updates
  Hash.sha3x224Init_eq Hash.sha3x256Init_eq Hash.sha3x384Init_eq Hash.sha3x512Init_eq
  Hash.shake128Init_eq Hash.shake256Init_eq Hash.keccak256Init_eq

-- Keccak-p is a permutation [FIPS 202, §3.3].
audit_axioms Hash.Keccak.keccakPState_bijective Hash.Keccak.keccakP_injective
  Hash.Keccak.keccakP_surjective

-- BLAKE2 constants: SHA-2 IVs, SIGMA rows are permutations [RFC 7693, §2.6, §2.7].
audit_axioms Hash.BLAKE2.blake2b_IV Hash.BLAKE2.blake2s_IV Hash.BLAKE2.SIGMA_perm

-- BLAKE2: the fast specification equals the reference [RFC 7693; EIP-152].
audit_axioms Hash.BLAKE2.Equiv.hashWith_eq Hash.BLAKE2.Equiv.F_eq Hash.BLAKE2.blake2bWith_eq
  Hash.BLAKE2.blake2sWith_eq Hash.BLAKE2.blake2b_eq Hash.BLAKE2.blake2s_eq Hash.BLAKE2.blake2bF_eq

-- BLAKE2: streaming equals one-shot.
audit_axioms Hash.BLAKE2.Fast.State.finalize_updates Hash.blake2bInit_eq Hash.blake2sInit_eq

-- BLAKE3: the fast specification equals the reference [BLAKE3, §2].
audit_axioms Hash.BLAKE3.Equiv.hashWith_eq Hash.BLAKE3.blake3Xof_eq Hash.BLAKE3.blake3_eq
  Hash.BLAKE3.blake3Keyed_eq Hash.BLAKE3.blake3DeriveKey_eq Hash.Tree.root_map
  Hash.BLAKE3.blake3Xof_prefix

-- BLAKE3: streaming equals one-shot [BLAKE3, §5.1].
audit_axioms Hash.BLAKE3.Fast.State.finalize_updates Hash.blake3Init_eq Hash.blake3KeyedInit_eq
  Hash.blake3DeriveKeyInit_eq

-- Constructions.
audit_axioms Hash.MerkleDamgard.iterate_append Hash.Sponge.sponge_prefix Hash.Tree.finish_pushAll

-- ZK-friendly hashes: the S-box, and Poseidon (fast = reference, ring homomorphisms, circomlib).
audit_axioms Hash.ZK.sbox_sbox_invExponent Hash.ZK.sbox_invExponent_sbox Hash.ZK.sbox_bijective
  Hash.ZK.Poseidon.Reference.map_permutation Hash.ZK.Poseidon.Fast.permutation_eq
  Hash.ZK.FieldOps.pow_eq Hash.ZK.FieldOps.Hom.ofRingHom Hash.ZK.Poseidon.Fast.map_permutation
  Hash.ZK.Poseidon.Circom.fastParams_toRef Hash.ZK.Poseidon.Circom.map_fastParams
  Hash.ZK.Poseidon.Circom.map_permutation_fastParams

-- Poseidon2: the fast linear layers are the matrices, the fast permutation computes the reference,
-- and the instances' fast parameters represent their specifications.
audit_axioms Hash.ZK.Poseidon2.Fast.externalM4_eq Hash.ZK.Poseidon2.Fast.permutation_eq
  Hash.ZK.Poseidon2.Fast.map_permutation Hash.ZK.Poseidon2.Plonky3.map_permutation_fastParams
  Hash.ZK.Poseidon2.map_permutation_hlBn254FastParams
