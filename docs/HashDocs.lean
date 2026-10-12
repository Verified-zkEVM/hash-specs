/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import VersoManual
import HashDocs.SHA2
import HashDocs.SHA3
import HashDocs.BLAKE2
import HashDocs.BLAKE3

open Verso.Genre Manual

#doc (Manual) "Hash: Formal Specifications of Hash Functions in Lean" =>
%%%
authors := ["Derek Sorensen"]
%%%

This book documents the `Hash` library: formal, executable specifications of cryptographic hash
functions in Lean 4. Each hash has a *reference* specification that transcribes its standard,
a *fast* specification proved equal to it, and a differential-testing harness that compares the
fast specification against independent implementations.

{include 1 HashDocs.SHA2}

{include 1 HashDocs.SHA3}

{include 1 HashDocs.BLAKE2}

{include 1 HashDocs.BLAKE3}
