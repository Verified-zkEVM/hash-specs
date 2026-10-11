/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import HashKAT.Rsp
public import Hash.SHA2.API

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

/-- A test file and the function it tests. -/
structure TestFile where
  /-- The path, relative to `HashKAT/vectors/`. -/
  path : String
  /-- The hash under test. -/
  hash : ByteArray → ByteArray
  /-- How to run the file. -/
  kind : Kind

/-- The SHAVS short-message, long-message and Monte Carlo files of one SHA-2 variant. -/
def shavs (name : String) (hash : ByteArray → ByteArray) : List TestFile :=
  [⟨s!"nist-cavp-shs/{name}ShortMsg.rsp", hash, .messages⟩,
   ⟨s!"nist-cavp-shs/{name}LongMsg.rsp", hash, .messages⟩,
   ⟨s!"nist-cavp-shs/{name}Monte.rsp", hash, .shavsMonte⟩]

/-- Every test file. -/
def testFiles : List TestFile :=
  shavs "SHA224" sha224 ++ shavs "SHA256" sha256 ++ shavs "SHA384" sha384 ++
  shavs "SHA512" sha512 ++ shavs "SHA512_224" sha512t224 ++ shavs "SHA512_256" sha512t256

public def main : IO UInt32 := do
  let mut total := 0
  let mut failed := 0
  for f in testFiles do
    let contents ← IO.FS.readFile ("HashKAT/vectors" / f.path)
    let outcome := match f.kind with
      | .messages => runMessageFile f.hash contents
      | .shavsMonte => runShavsMonte f.hash contents
    total := total + outcome.passed + outcome.failures.length
    failed := failed + outcome.failures.length
    let status := if outcome.failures.isEmpty then "ok" else "FAILED"
    IO.println s!"{status}  {f.path}: {outcome.passed} passed, {outcome.failures.length} failed"
    for e in outcome.failures.take 5 do
      IO.println s!"        {e}"
  if failed == 0 then
    IO.println s!"all {total} known-answer tests passed"
    return 0
  else
    IO.println s!"{failed} of {total} known-answer tests failed"
    return 1
