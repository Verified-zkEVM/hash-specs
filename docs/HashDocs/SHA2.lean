/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import VersoManual
import Hash.SHA2.API
import HashDocs.Bibliography

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open HashDocs.Bib

set_option pp.rawOnError true

#doc (Manual) "SHA-2" =>
%%%
tag := "sha2"
%%%

SHA-2 is the family of hash functions standardised by NIST in FIPS 180-4, the *Secure Hash
Standard* ([doi:10.6028/NIST.FIPS.180-4](https://doi.org/10.6028/NIST.FIPS.180-4)). Its members
are SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256. The first machine-checked
proof that a production implementation meets this standard was Appel's Coq verification of
OpenSSL's SHA-256 {citep appel2015}[].

_This chapter is a skeleton. Phase 1 of the roadmap fills it in following the chapter template._

# The round function

Each block is processed in 64 rounds (SHA-224/256) or 80 rounds (SHA-384/512/t). One round
updates the eight working variables $`a, …, h` (FIPS 180-4, §6.2.2, step 3):

![One round of the SHA-2 compression function](../static/sha2-round.svg)

# Checked examples

Code in this book is elaborated against the library, so it cannot drift from the definitions.
For instance, the SHA-256 digest of `abc` from the NIST examples is checked by the kernel when
the book is built:

```lean
open Hash in
example :
    (sha256 ⟨#[0x61, 0x62, 0x63]⟩).toHex =
      "ba7816bf8f01cfea414140de5dae2223" ++
      "b00361a396177a9cb410ff61f20015ad" := by
  decide +kernel
```
