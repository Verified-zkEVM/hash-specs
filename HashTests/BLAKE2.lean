/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

import Hash.BLAKE2.API

/-!
# BLAKE2 known-answer tests (kernel-checked)

A small representative subset of known answers, checked by the kernel with `decide +kernel`: the
examples of RFC 7693 Appendices A and B, the first keyed vector of the BLAKE2 team's
`blake2-kat.json`, and EIP-152 test vector 5. The full suites run in `hash-kat`.
-/

namespace HashTests.BLAKE2

open Hash

set_option maxRecDepth 100000

/-- The bytes of a string literal known to be ASCII. -/
def ascii (s : String) : ByteArray := ⟨(s.toList.map fun c => c.toNat.toUInt8).toArray⟩

example : (blake2b (ascii "abc")).toHex =
    "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
    "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923" := by
  decide +kernel

example : (blake2s (ascii "abc")).toHex =
    "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982" := by
  decide +kernel

example : (blake2bWith ⟨((List.range 64).map (·.toUInt8)).toArray⟩ .empty .empty 64
      .empty).toHex =
    "10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786" ++
    "b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568" := by
  decide +kernel

/-- EIP-152 test vector 5: the RFC 7693 `abc` block, 12 rounds, final. -/
example : ((ByteArray.ofHex? (
      "0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f" ++
      "3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e13" ++
      "19cde05b61626300000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "000000000300000000000000000000000000000001")).map
      fun i => (blake2bPrecompile i).toOption.map ByteArray.toHex) =
    some (some ("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
      "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")) := by
  decide +kernel

end HashTests.BLAKE2
