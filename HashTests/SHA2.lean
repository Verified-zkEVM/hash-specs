/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

import Hash.SHA2.API

/-!
# SHA-2 known-answer tests (kernel-checked)

A small representative subset of known answers, checked by the kernel with `decide +kernel`. The
full NIST CAVP suites run in the compiled `hash-specs-kat` executable.

The examples are the one-block and two-block messages of the NIST examples
(<https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines/example-values>).
-/

namespace HashTests.SHA2

open Hash

/-- The bytes of a string literal known to be ASCII. -/
def ascii (s : String) : ByteArray := ⟨(s.toList.map fun c => c.toNat.toUInt8).toArray⟩

example : (sha256 (ascii "abc")).toHex =
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by decide +kernel

example : (sha224 (ascii "abc")).toHex =
    "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7" := by decide +kernel

example : (sha256 (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")).toHex =
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by decide +kernel

example : (sha512 (ascii "abc")).toHex =
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a" ++
    "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f" := by decide +kernel

example : (sha384 (ascii "abc")).toHex =
    "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded163" ++
    "1a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7" := by decide +kernel

example : (sha512t224 (ascii "abc")).toHex =
    "4634270f707b6a54daae7530460842e20e37ed265ceee9a43e8924aa" := by decide +kernel

example : (sha512t256 (ascii "abc")).toHex =
    "53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23" := by decide +kernel

example : (sha256 ByteArray.empty).toHex =
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by decide +kernel

end HashTests.SHA2
