/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Init

/-!
# The Grain LFSR used for parameter generation

Poseidon, Poseidon2 and their instances derive their round constants (and Poseidon its Cauchy
matrix) from an 80-bit Grain LFSR in self-shrinking mode, as described in the Poseidon full
version, appendix "Initialization of the Grain LFSR Used for Parameter Generation" [Poseidon,
App. E], and implemented by the reference script `generate_parameters_grain.sage` [hadeshash].

* The initial state `b₀ … b₇₉` is the concatenation, most significant bit first, of the field
  type (2 bits), the S-box code (4 bits), the field size `n` in bits (12 bits), the width `t`
  (12 bits), `R_F` (10 bits), `R_P` (10 bits), and thirty ones.
* Each clock computes `b_{i+80} = b_{i+62} ⊕ b_{i+51} ⊕ b_{i+38} ⊕ b_{i+23} ⊕ b_{i+13} ⊕ b_i`
  and outputs it; the first 160 outputs are discarded.
* Self-shrinking: output bits are taken in pairs; if the first is 1 the second is output,
  otherwise both are discarded.
* A field element is `n` output bits read most significant first, sampled again while it is not
  below `p`.

The state is a natural number below `2⁸⁰` whose most significant bit is `b₀`. Loops carry a
fuel argument so that the definitions are total and reduce in the kernel; `nextBit` would need
more than a thousand consecutive discarded pairs to run out, which does not happen for any
instance in this library (their constants are checked against the published tables).

Two encodings of the S-box exist in practice: the reference script (and circomlib) uses code 0
for `x ^ α`, while Filecoin's Neptune uses 1 for `x ^ 5`. The code is therefore a parameter.

## References

* [Poseidon] L. Grassi, D. Khovratovich, C. Rechberger, A. Roy, M. Schofnegger, *Poseidon: A New
  Hash Function for Zero-Knowledge Proof Systems*, USENIX Security 2021; full version ePrint
  2019/458. <https://eprint.iacr.org/2019/458>
* [hadeshash] The Poseidon reference implementation, `code/generate_parameters_grain.sage`,
  commit 208b5a164c6a252b137997694d90931b2bb851c5.
  <https://extgit.iaik.tugraz.at/krypto/hadeshash>
-/

@[expose] public section

namespace Hash.ZK.Grain

/-- The fields of the initial Grain state [Poseidon, App. E]. -/
structure Params where
  /-- The field type: 1 for a prime field `𝔽_p`, 0 for a binary field. -/
  field : ℕ
  /-- The S-box code (0 for `x ^ α` in the reference script). -/
  sbox : ℕ
  /-- The size of a field element in bits. -/
  n : ℕ
  /-- The width `t` of the permutation. -/
  t : ℕ
  /-- The number of full rounds. -/
  RF : ℕ
  /-- The number of partial rounds. -/
  RP : ℕ

/-- Bit `b_i` of the state. -/
def bit (s i : ℕ) : ℕ := (s >>> (79 - i)) &&& 1

/-- One clock: the new bit `b_{80} = b_{62} ⊕ b_{51} ⊕ b_{38} ⊕ b_{23} ⊕ b_{13} ⊕ b_0`, and the
state shifted by one. -/
def clock (s : ℕ) : ℕ × ℕ :=
  let b := bit s 62 ^^^ bit s 51 ^^^ bit s 38 ^^^ bit s 23 ^^^ bit s 13 ^^^ bit s 0
  (b, ((s <<< 1) &&& (2 ^ 80 - 1)) ||| b)

/-- Clock `k` times, discarding the output. -/
def discard : ℕ → ℕ → ℕ
  | 0, s => s
  | k + 1, s => discard k (clock s).2

/-- The state after initialization and the 160 discarded clocks [Poseidon, App. E]. -/
def init (g : Params) : ℕ :=
  discard 160 <|
    (((((g.field <<< 4 ||| g.sbox) <<< 12 ||| g.n) <<< 12 ||| g.t) <<< 10 ||| g.RF) <<< 10
      ||| g.RP) <<< 30 ||| (2 ^ 30 - 1)

/-- The next bit of the self-shrinking generator: clock twice, and output the second bit if the
first is 1 [Poseidon, App. E]. -/
def nextBit : ℕ → ℕ → ℕ × ℕ
  | 0, s => (0, s)
  | fuel + 1, s =>
    match clock s with
    | (b₁, s) =>
      match clock s with
      | (b₂, s) => if b₁ = 1 then (b₂, s) else nextBit fuel s

/-- `k` output bits, most significant first, appended to `acc`. -/
def bits : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, acc, s => (acc, s)
  | k + 1, acc, s =>
    match nextBit 1000 s with
    | (b, s) => bits k (2 * acc + b) s

/-- An `n`-bit number below `p`, sampled again while it is not [Poseidon, App. E]. -/
def sampleBelow (p n : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, s => (0, s)
  | fuel + 1, s =>
    match bits n 0 s with
    | (v, s) => if v < p then (v, s) else sampleBelow p n fuel s

/-- `k` field elements sampled below `p`, and the state after them. -/
def sampleList (p n : ℕ) : ℕ → ℕ → List ℕ × ℕ
  | 0, s => ([], s)
  | k + 1, s =>
    match sampleBelow p n 1000 s with
    | (v, s) =>
      match sampleList p n k s with
      | (vs, s) => (v :: vs, s)

/-- `k` numbers of `n` bits each, reduced modulo `p` (no rejection), and the state after them:
the samples from which the reference script builds its Cauchy matrix. -/
def rawList (p n : ℕ) : ℕ → ℕ → List ℕ × ℕ
  | 0, s => ([], s)
  | k + 1, s =>
    match bits n 0 s with
    | (v, s) =>
      match rawList p n k s with
      | (vs, s) => (v % p :: vs, s)

end Hash.ZK.Grain
