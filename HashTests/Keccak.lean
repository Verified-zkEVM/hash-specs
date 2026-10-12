/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

import Hash.Keccak.API

/-!
# SHA-3, SHAKE and Keccak-256 known-answer tests (kernel-checked)

A small representative subset of known answers, checked by the kernel with `decide +kernel`. The
full NIST CAVP SHA3VS suites run in the compiled `hash-kat` executable.

The SHA-3 and SHAKE values are from the NIST examples
(<https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines/example-values>); the
Keccak-256 value of the empty string is the well-known Ethereum constant `KECCAK_EMPTY`.
-/

namespace HashTests.Keccak

open Hash

/-- The bytes of a string literal known to be ASCII. -/
def ascii (s : String) : ByteArray := ⟨(s.toList.map fun c => c.toNat.toUInt8).toArray⟩

example : (sha3x256 ByteArray.empty).toHex =
    "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a" := by decide +kernel

example : (sha3x224 (ascii "abc")).toHex =
    "e642824c3f8cf24ad09234ee7d3c766fc9a3a5168d0c94ad73b46fdf" := by decide +kernel

example : (sha3x512 (ascii "abc")).toHex =
    "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e" ++
    "10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0" := by decide +kernel

example : (shake128 ByteArray.empty 32).toHex =
    "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26" := by decide +kernel

example : (keccak256 ByteArray.empty).toHex =
    "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470" := by decide +kernel

end HashTests.Keccak
