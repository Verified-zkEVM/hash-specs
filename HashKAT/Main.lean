/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import HashKAT.Rsp
public import Hash.SHA2.API
public import Hash.Keccak.API
public import HashFFI.Export

/-!
# Known-answer test runner

Runs the full official test suites against the fast specifications. The vectors are vendored in
`HashKAT/vectors/` (see the README there for their provenance). Run from the repository root:

```
lake exe hash-kat
```
-/

open Hash HashKAT

/-- How a test file is run. -/
inductive Kind where
  /-- `Len`/`Msg`/`MD` records. -/
  | messages
  /-- The SHAVS Monte Carlo test. -/
  | shavsMonte
  /-- The SHA3VS Monte Carlo test for the SHA-3 hash functions. -/
  | sha3Monte
  /-- `Msg`/`Output` records of an extendable-output function. -/
  | xof (f : ByteArray → Nat → ByteArray)
  /-- The SHA3VS Monte Carlo test for SHAKE. -/
  | shakeMonte (f : ByteArray → Nat → ByteArray)

/-- A test file and the function it tests. -/
structure TestFile where
  /-- The path, relative to `HashKAT/vectors/`. -/
  path : String
  /-- The hash under test. -/
  hash : ByteArray → ByteArray
  /-- How to run the file. -/
  kind : Kind
  /-- Whether `hash` uses the streaming interface (for the report only). -/
  streaming : Bool := false

/-- The SHAVS short-message, long-message and Monte Carlo files of one SHA-2 variant. -/
def shavs (name : String) (hash : ByteArray → ByteArray) : List TestFile :=
  [⟨s!"nist-cavp-shs/{name}ShortMsg.rsp", hash, .messages, false⟩,
   ⟨s!"nist-cavp-shs/{name}LongMsg.rsp", hash, .messages, false⟩,
   ⟨s!"nist-cavp-shs/{name}Monte.rsp", hash, .shavsMonte, false⟩]

/-- The piece-size patterns used to test streaming: single bytes, sizes around the block
boundaries of both word sizes, and an empty update between pieces. -/
def piecePatterns : List (List Nat) :=
  [[1], [7, 0, 13], [63, 64, 65], [127, 128, 129], [3, 200]]

/-- Hash `m` incrementally under every pattern of `piecePatterns`. The result is the common
digest if all patterns agree, and the empty array (which matches no test vector) otherwise. -/
def streamed {α : Type} [SHA2.Fast.Word α] (s : SHA2.Fast.State α) (m : ByteArray) :
    ByteArray :=
  let digests := piecePatterns.map (HashFFI.streamPieces s · m)
  match digests with
  | d :: ds => if ds.all (· == d) then d else ByteArray.empty
  | [] => ByteArray.empty

/-- The SHAVS short- and long-message files of one SHA-2 variant, hashed incrementally. -/
def shavsStreamed {α : Type} [SHA2.Fast.Word α] (name : String) (s : SHA2.Fast.State α) :
    List TestFile :=
  [⟨s!"nist-cavp-shs/{name}ShortMsg.rsp", streamed s, .messages, true⟩,
   ⟨s!"nist-cavp-shs/{name}LongMsg.rsp", streamed s, .messages, true⟩]

/-- The SHA3VS files of one SHA-3 hash function. -/
def sha3vs (name : String) (hash : ByteArray → ByteArray) : List TestFile :=
  [⟨s!"nist-cavp-sha3/{name}ShortMsg.rsp", hash, .messages, false⟩,
   ⟨s!"nist-cavp-sha3/{name}LongMsg.rsp", hash, .messages, false⟩,
   ⟨s!"nist-cavp-sha3/{name}Monte.rsp", hash, .sha3Monte, false⟩]

/-- The SHA3VS files of one SHAKE function. -/
def shakevs (name : String) (xof : ByteArray → Nat → ByteArray) : List TestFile :=
  [⟨s!"nist-cavp-sha3/{name}ShortMsg.rsp", id, .xof xof, false⟩,
   ⟨s!"nist-cavp-sha3/{name}LongMsg.rsp", id, .xof xof, false⟩,
   ⟨s!"nist-cavp-sha3/{name}VariableOut.rsp", id, .xof xof, false⟩,
   ⟨s!"nist-cavp-sha3/{name}Monte.rsp", id, .shakeMonte xof, false⟩]

/-- Every test file. -/
def testFiles : List TestFile :=
  shavs "SHA224" sha224 ++ shavs "SHA256" sha256 ++ shavs "SHA384" sha384 ++
  shavs "SHA512" sha512 ++ shavs "SHA512_224" sha512t224 ++ shavs "SHA512_256" sha512t256 ++
  shavsStreamed "SHA224" sha224Init ++ shavsStreamed "SHA256" sha256Init ++
  shavsStreamed "SHA384" sha384Init ++ shavsStreamed "SHA512" sha512Init ++
  shavsStreamed "SHA512_224" sha512t224Init ++ shavsStreamed "SHA512_256" sha512t256Init ++
  sha3vs "SHA3_224" sha3x224 ++ sha3vs "SHA3_256" sha3x256 ++ sha3vs "SHA3_384" sha3x384 ++
  sha3vs "SHA3_512" sha3x512 ++ shakevs "SHAKE128" shake128 ++ shakevs "SHAKE256" shake256

public def main : IO UInt32 := do
  let mut total := 0
  let mut failed := 0
  for f in testFiles do
    let contents ← IO.FS.readFile ("HashKAT/vectors" / f.path)
    let outcome := match f.kind with
      | .messages => runMessageFile f.hash contents
      | .shavsMonte => runShavsMonte f.hash contents
      | .sha3Monte => runSha3Monte f.hash contents
      | .xof xof => runXofFile xof contents
      | .shakeMonte xof => runShakeMonte xof contents
    total := total + outcome.passed + outcome.failures.length
    failed := failed + outcome.failures.length
    let status := if outcome.failures.isEmpty then "ok" else "FAILED"
    let mode := match f.kind with
      | .messages => if f.streaming then " (streamed)" else ""
      | _ => ""
    IO.println s!"{status}  {f.path}{mode}: {outcome.passed} passed, {outcome.failures.length} failed"
    for e in outcome.failures.take 5 do
      IO.println s!"        {e}"
  if failed == 0 then
    IO.println s!"all {total} known-answer tests passed"
    return 0
  else
    IO.println s!"{failed} of {total} known-answer tests failed"
    return 1
