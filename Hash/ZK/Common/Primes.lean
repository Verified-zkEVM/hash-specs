/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Init

/-!
# The primes of the ZK-friendly instances

The moduli of the prime fields over which the instances in `Hash.ZK` are defined. The
specifications work in `ZMod p`; CompPoly (Layer 2, `HashZK`) supplies fast representations of the
same fields and the primality certificates.

## References

* [BN254] P. Barreto, M. Naehrig, *Pairing-Friendly Elliptic Curves of Prime Order*, SAC 2005;
  the alt_bn128 instance of EIP-196. <https://eips.ethereum.org/EIPS/eip-196>
* [Plonky3] The Plonky3 toolkit, `baby-bear` and `koala-bear` crates.
  <https://github.com/Plonky3/Plonky3>
-/

@[expose] public section

namespace Hash.ZK

/-- The order `r` of the BN254 (alt_bn128) groups: the scalar field of BN254, and the base field of
BabyJubJub and Grumpkin [BN254; EIP-196]. -/
def bn254 : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- The BabyBear prime `2³¹ − 2²⁷ + 1` [Plonky3]. -/
def babyBear : ℕ := 2 ^ 31 - 2 ^ 27 + 1

/-- The KoalaBear prime `2³¹ − 2²⁴ + 1` [Plonky3]. -/
def koalaBear : ℕ := 2 ^ 31 - 2 ^ 24 + 1

/-- The Goldilocks prime `2⁶⁴ − 2³² + 1`. -/
def goldilocks : ℕ := 2 ^ 64 - 2 ^ 32 + 1

end Hash.ZK
