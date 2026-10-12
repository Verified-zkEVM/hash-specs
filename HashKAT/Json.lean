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

Runners for the BLAKE2 team's `blake2-kat.json` (a list of records with fields `hash`, `in`,
`key` and `out`, as hexadecimal strings) and the BLAKE3 team's `test_vectors.json`.
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

/-- The BLAKE3 test input of length `n`: the bytes `0, 1, …, 250` repeated. -/
def blake3Input (n : Nat) : ByteArray := ⟨((List.range n).map fun i => (i % 251).toUInt8).toArray⟩

/-- The bytes of an ASCII string. -/
def asciiBytes (s : String) : ByteArray := ⟨(s.toList.map fun c => c.toNat.toUInt8).toArray⟩

/-- Check one mode of `test_vectors.json` (`hash`, `keyed_hash` or `derive_key`), with
`xof key context message outputLength` given the file's key and context string. Each case is
checked at the full output length and at 32 bytes. -/
def runBlake3Json (mode : String)
    (xof : ByteArray → ByteArray → ByteArray → Nat → ByteArray) (contents : String) :
    Outcome := Id.run do
  let .ok json := Json.parse contents | return ⟨0, ["bad JSON"]⟩
  let .ok key := json.getObjValAs? String "key" | return ⟨0, ["missing key"]⟩
  let .ok context := json.getObjValAs? String "context_string" |
    return ⟨0, ["missing context string"]⟩
  let .ok cases := (json.getObjVal? "cases").bind Json.getArr? |
    return ⟨0, ["missing cases"]⟩
  let mut passed := 0
  let mut failures : List String := []
  for c in cases do
    match (c.getObjValAs? Nat "input_len").toOption,
        ((c.getObjValAs? String mode).toOption).bind ByteArray.ofHex? with
    | some n, some out =>
      let f := xof (asciiBytes key) (asciiBytes context) (blake3Input n)
      if f out.size == out && f 32 == out.extract 0 32 then passed := passed + 1
      else failures := s!"input length {n}" :: failures
    | _, _ => failures := "bad case" :: failures
  return ⟨passed, failures.reverse⟩

/-- Check the records of a Poseidon vector file: lists of `initState`, `inputs` and asserted
`outputs` (pairs of an output index and a value), all decimal strings, with
`hash initState inputs nOut` returning the first `nOut` output elements. -/
def runPoseidonJson (hash : Nat → List Nat → Nat → List Nat) (contents : String) : Outcome :=
  Id.run do
  let .ok json := Json.parse contents | return ⟨0, ["bad JSON"]⟩
  let .ok records := json.getArr? | return ⟨0, ["expected a JSON array"]⟩
  let mut passed := 0
  let mut failures : List String := []
  let mut i := 0
  for r in records do
    i := i + 1
    let num (j : Json) : Option Nat := (j.getStr?.toOption).bind String.toNat?
    let (.ok init, .ok ins, .ok outs) := (r.getObjValAs? String "initState",
        (r.getObjVal? "inputs").bind Json.getArr?, (r.getObjVal? "outputs").bind Json.getArr?)
      | failures := s!"record {i}: bad fields" :: failures; continue
    let inputs := ins.toList.filterMap num
    let expected : List (Nat × Nat) := outs.toList.filterMap fun o =>
      match (o.getArrVal? 0).toOption.bind (·.getNat?.toOption),
          (o.getArrVal? 1).toOption.bind num with
      | some idx, some v => some (idx, v)
      | _, _ => none
    match init.toNat? with
    | some init =>
      let nOut := expected.foldl (fun n e => max n (e.1 + 1)) 0
      let got := hash init inputs nOut
      if expected.all (fun e => got.getD e.1 0 == e.2) && inputs.length == ins.size then
        passed := passed + 1
      else failures := s!"record {i} ({inputs.length} inputs)" :: failures
    | none => failures := s!"record {i}: bad initState" :: failures
  return ⟨passed, failures.reverse⟩

end HashKAT
