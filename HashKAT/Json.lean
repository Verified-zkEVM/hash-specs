/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import HashKAT.Rsp
public import Lean.Data.Json

/-!
# JSON test vectors

A runner for the BLAKE2 team's `blake2-kat.json`: a list of records with fields `hash`, `in`,
`key` and `out` (hexadecimal strings).
-/

public section

namespace HashKAT

open Lean Hash

/-- Check the records of `blake2-kat.json` whose `hash` field is `name`, with
`hash key message outputLength`. -/
def runBlake2Json (name : String) (hash : ByteArray → ByteArray → Nat → ByteArray)
    (contents : String) : Outcome := Id.run do
  let .ok json := Json.parse contents | return ⟨0, ["bad JSON"]⟩
  let .ok records := json.getArr? | return ⟨0, ["expected a JSON array"]⟩
  let mut passed := 0
  let mut failures : List String := []
  let mut i := 0
  for r in records do
    i := i + 1
    let field (k : String) : Option String := (r.getObjValAs? String k).toOption
    if field "hash" != some name then continue
    match (field "in").bind ByteArray.ofHex?, (field "key").bind ByteArray.ofHex?,
        (field "out").bind ByteArray.ofHex? with
    | some m, some key, some out =>
      if hash key m out.size == out then passed := passed + 1
      else failures := s!"record {i}" :: failures
    | _, _, _ => failures := s!"record {i}: bad fields" :: failures
  return ⟨passed, failures.reverse⟩

end HashKAT
