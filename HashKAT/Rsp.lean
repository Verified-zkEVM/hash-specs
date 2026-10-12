/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Prelude.Bytes

/-!
# NIST CAVP response files

A parser for the `.rsp` files of NIST's Cryptographic Algorithm Validation Program, and the test
procedures of the Secure Hash Algorithm Validation System (SHAVS) and the SHA-3 Validation System
(SHA3VS). A response file is a sequence of `key = value` lines, grouped into records by blank
lines; `[…]` lines set parameters for the records that follow.
-/

public section

namespace HashKAT

open Hash

/-- One record of a response file: its `key = value` pairs, plus the `[key = value]` parameters
in force. -/
structure Record where
  /-- The record's fields. -/
  fields : List (String × String)
  /-- The bracketed parameters in force for this record. -/
  params : List (String × String)

/-- The value of a field. -/
def Record.get? (r : Record) (key : String) : Option String :=
  (r.fields.find? (·.1 == key)).map (·.2)

/-- Split `key = value` (with optional surrounding brackets) into its parts. -/
def parseKeyValue (line : String) : Option (String × String) :=
  let line := String.ofList (line.toList.filter fun c => c != '[' && c != ']')
  match line.splitOn "=" with
  | [k, v] => some (k.trimAscii.toString, v.trimAscii.toString)
  | _ => none

/-- Parse the records of a response file. Comment lines start with `#`. -/
def parseRecords (contents : String) : List Record := Id.run do
  let mut records : Array Record := #[]
  let mut params : List (String × String) := []
  let mut current : List (String × String) := []
  for raw in contents.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then
      if !current.isEmpty then
        records := records.push ⟨current.reverse, params⟩
        current := []
    else if line.startsWith "[" then
      if let some kv := parseKeyValue line then
        params := kv :: params.filter (·.1 != kv.1)
    else if let some kv := parseKeyValue line then
      current := kv :: current
  if !current.isEmpty then
    records := records.push ⟨current.reverse, params⟩
  return records.toList

/-- Decode a hexadecimal field, failing loudly. -/
def hexField (r : Record) (key : String) : Except String ByteArray := do
  let some s := r.get? key | throw s!"missing field {key}"
  let some b := ByteArray.ofHex? s | throw s!"bad hexadecimal in field {key}"
  return b

/-- The message of a `Len`/`Msg` record. Byte-oriented files encode the empty message as
`Len = 0`, `Msg = 00`. Records without `Len` (SHA3VS variable-output files) use the whole `Msg`. -/
def message (r : Record) : Except String ByteArray := do
  let some len := (r.get? "Len").bind String.toNat? | hexField r "Msg"
  if len % 8 != 0 then throw s!"bit-oriented message of length {len}"
  let msg ← hexField r "Msg"
  return msg.extract 0 (len / 8)

/-- The outcome of running one test file. -/
structure Outcome where
  /-- The number of records checked. -/
  passed : Nat
  /-- Descriptions of the failures. -/
  failures : List String

/-- Check every `Len`/`Msg`/`MD` record of a short- or long-message file. -/
def runMessageFile (hash : ByteArray → ByteArray) (contents : String) : Outcome := Id.run do
  let mut passed := 0
  let mut failures : List String := []
  for r in parseRecords contents do
    if (r.get? "Msg").isNone then continue
    match message r, hexField r "MD" with
    | .ok m, .ok md =>
      if hash m == md then passed := passed + 1
      else failures := s!"Len = {r.get? "Len" |>.getD "?"}" :: failures
    | .error e, _ | _, .error e => failures := e :: failures
  return ⟨passed, failures.reverse⟩

/-- The SHAVS Monte Carlo test [SHAVS, §6.4]: from a seed, 100 checkpoints, each the result of
1000 chained hashes `MDᵢ = H(MDᵢ₋₃ ‖ MDᵢ₋₂ ‖ MDᵢ₋₁)`. -/
def runShavsMonte (hash : ByteArray → ByteArray) (contents : String) : Outcome := Id.run do
  let records := parseRecords contents
  let some seedRecord := records.find? (·.get? "Seed" |>.isSome)
    | return ⟨0, ["no seed"]⟩
  let .ok seed := hexField seedRecord "Seed" | return ⟨0, ["bad seed"]⟩
  let mut seed := seed
  let mut passed := 0
  let mut failures : List String := []
  for r in records do
    let some count := r.get? "COUNT" | continue
    let .ok expected := hexField r "MD" | failures := s!"COUNT = {count}: bad MD" :: failures
    let mut md0 := seed
    let mut md1 := seed
    let mut md2 := seed
    for _ in [0:1000] do
      let md3 := hash (md0 ++ md1 ++ md2)
      md0 := md1
      md1 := md2
      md2 := md3
    seed := md2
    if md2 == expected then passed := passed + 1
    else failures := s!"COUNT = {count}" :: failures
  return ⟨passed, failures.reverse⟩

/-- The value of a parameter `[key = value]`, as a number. -/
def Record.param? (r : Record) (key : String) : Option Nat :=
  ((r.params.find? (·.1 == key)).map (·.2)).bind String.toNat?

/-- Check every `Msg`/`Output` record of a SHAKE file [SHA3VS, §6.3.1, §6.3.2]. The output length
in bits is the record's `Outputlen`, or the `[Outputlen = …]` parameter. -/
def runXofFile (xof : ByteArray → Nat → ByteArray) (contents : String) : Outcome := Id.run do
  let mut passed := 0
  let mut failures : List String := []
  for r in parseRecords contents do
    if (r.get? "Msg").isNone then continue
    let outBits := ((r.get? "Outputlen").bind String.toNat?).orElse fun _ => r.param? "Outputlen"
    let some outBits := outBits | failures := "missing Outputlen" :: failures; continue
    match message r, hexField r "Output" with
    | .ok m, .ok out =>
      if xof m (outBits / 8) == out then passed := passed + 1
      else failures := s!"COUNT/Len = {(r.get? "COUNT").getD ((r.get? "Len").getD "?")}" :: failures
    | .error e, _ | _, .error e => failures := e :: failures
  return ⟨passed, failures.reverse⟩

/-- The SHA-3 Monte Carlo test [SHA3VS, §6.2.3]: from a seed, 100 checkpoints, each the result of
1000 iterated hashes `MDᵢ = H(MDᵢ₋₁)`. -/
def runSha3Monte (hash : ByteArray → ByteArray) (contents : String) : Outcome := Id.run do
  let records := parseRecords contents
  let some seedRecord := records.find? (·.get? "Seed" |>.isSome)
    | return ⟨0, ["no seed"]⟩
  let .ok seed := hexField seedRecord "Seed" | return ⟨0, ["bad seed"]⟩
  let mut md := seed
  let mut passed := 0
  let mut failures : List String := []
  for r in records do
    let some count := r.get? "COUNT" | continue
    let .ok expected := hexField r "MD" | failures := s!"COUNT = {count}: bad MD" :: failures
    for _ in [0:1000] do
      md := hash md
    if md == expected then passed := passed + 1
    else failures := s!"COUNT = {count}" :: failures
  return ⟨passed, failures.reverse⟩

/-- The SHAKE Monte Carlo test [SHA3VS, §6.3.3]. Each of 100 checkpoints is the result of 1000
iterations, where each iteration hashes the leftmost 128 bits of the previous output, and the
next output length is derived from the rightmost 16 bits of the current output. -/
def runShakeMonte (xof : ByteArray → Nat → ByteArray) (contents : String) : Outcome := Id.run do
  let records := parseRecords contents
  let some msgRecord := records.find? (·.get? "Msg" |>.isSome)
    | return ⟨0, ["no Msg"]⟩
  let .ok msg := hexField msgRecord "Msg" | return ⟨0, ["bad Msg"]⟩
  let some minBits := msgRecord.param? "Minimum Output Length (bits)"
    | return ⟨0, ["no minimum output length"]⟩
  let some maxBits := msgRecord.param? "Maximum Output Length (bits)"
    | return ⟨0, ["no maximum output length"]⟩
  let minBytes := minBits / 8
  let maxBytes := maxBits / 8
  let range := maxBytes - minBytes + 1
  let mut outLen := maxBytes
  let mut out := msg
  let mut passed := 0
  let mut failures : List String := []
  for r in records do
    let some count := r.get? "COUNT" | continue
    let .ok expected := hexField r "Output" | failures := s!"COUNT = {count}: bad Output" :: failures
    let some expectedLen := (r.get? "Outputlen").bind String.toNat?
      | failures := s!"COUNT = {count}: bad Outputlen" :: failures
    let mut lastLen := outLen
    for _ in [0:1000] do
      -- The leftmost 128 bits of the previous output, padded with zero bytes if shorter.
      let m := out.extract 0 16 ++ ByteArray.zeros (16 - min 16 out.size)
      lastLen := outLen
      out := xof m outLen
      let n := out.size
      let rightmost := 256 * (out.get! (n - 2)).toNat + (out.get! (n - 1)).toNat
      outLen := minBytes + rightmost % range
    if out == expected && 8 * lastLen == expectedLen then passed := passed + 1
    else failures := s!"COUNT = {count}" :: failures
  return ⟨passed, failures.reverse⟩

end HashKAT
