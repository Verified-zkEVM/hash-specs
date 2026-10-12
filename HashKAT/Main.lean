/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import HashKAT.Rsp
public import Hash.SHA2.API
public import Hash.Keccak.API
public import Hash.BLAKE2.API
public import Hash.BLAKE3.API
public import HashKAT.Json
public import HashFFI.Export
public import HashZK

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
  /-- Records of `blake2-kat.json` for one function: `hash key message outputLength`. -/
  | blake2Json (name : String) (f : ByteArray → ByteArray → Nat → ByteArray)
  /-- One mode of the BLAKE3 test vectors: `xof key context message outputLength`. -/
  | blake3Json (mode : String) (f : ByteArray → ByteArray → ByteArray → Nat → ByteArray)
  /-- EIP-152 records for the BLAKE2b `F` precompile. -/
  | eip152 (f : ByteArray → Except String ByteArray)
  /-- Poseidon records: `hash initState inputs nOut`, on natural numbers below the modulus. -/
  | poseidonJson (name : String) (f : Nat → List Nat → Nat → List Nat)
  /-- Permutation records: `perm instance input`, on natural numbers below the modulus. -/
  | permutationJson (name : String) (f : String → List Nat → Option (List Nat))

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

/-- Hash `m` incrementally with the Keccak state `s` under every pattern of `piecePatterns`,
squeezing `d` bytes. The result is the common output if all patterns agree, and the empty array
(which matches no test vector) otherwise. -/
def keccakStreamed (s : Keccak.Fast.State) (m : ByteArray) (d : Nat) : ByteArray :=
  let outs := piecePatterns.map (HashFFI.keccakStreamPieces s · m d)
  match outs with
  | o :: os => if os.all (· == o) then o else ByteArray.empty
  | [] => ByteArray.empty

/-- The SHA3VS short- and long-message files of one SHA-3 hash function, hashed incrementally. -/
def sha3vsStreamed (name : String) (s : Keccak.Fast.State) : List TestFile :=
  [⟨s!"nist-cavp-sha3/{name}ShortMsg.rsp", (keccakStreamed s · s.outLen), .messages, true⟩,
   ⟨s!"nist-cavp-sha3/{name}LongMsg.rsp", (keccakStreamed s · s.outLen), .messages, true⟩]

/-- The SHA3VS message files of one SHAKE function, hashed incrementally. -/
def shakevsStreamed (name : String) (s : Keccak.Fast.State) : List TestFile :=
  [⟨s!"nist-cavp-sha3/{name}ShortMsg.rsp", id, .xof (keccakStreamed s), true⟩,
   ⟨s!"nist-cavp-sha3/{name}LongMsg.rsp", id, .xof (keccakStreamed s), true⟩,
   ⟨s!"nist-cavp-sha3/{name}VariableOut.rsp", id, .xof (keccakStreamed s), true⟩]

/-- Hash `m` incrementally with the BLAKE2 state `s` under every pattern of `piecePatterns`.
The result is the common digest if all patterns agree, and the empty array otherwise. -/
def blake2Streamed {α : Type} [BLAKE2.Fast.Word α] (s : BLAKE2.Fast.State α) (m : ByteArray) :
    ByteArray :=
  let digests := piecePatterns.map (HashFFI.blake2StreamPieces s · m)
  match digests with
  | d :: ds => if ds.all (· == d) then d else ByteArray.empty
  | [] => ByteArray.empty

/-- Hash `m` incrementally with the BLAKE3 state `s` under every pattern of `piecePatterns`,
producing `d` bytes. The result is the common output if all patterns agree, and the empty array
otherwise. -/
def blake3Streamed (s : BLAKE3.Fast.State) (m : ByteArray) (d : Nat) : ByteArray :=
  let outs := (piecePatterns ++ [[1024], [1023, 1025], [5000]]).map
    (HashFFI.blake3StreamPieces s · m d)
  match outs with
  | o :: os => if os.all (· == o) then o else ByteArray.empty
  | [] => ByteArray.empty

/-- The three modes of the BLAKE3 test vectors, one-shot and streamed. -/
def blake3Files : List TestFile :=
  let file := "blake3/test_vectors.json"
  [⟨file, id, .blake3Json "hash" fun _ _ m d => blake3Xof m d, false⟩,
   ⟨file, id, .blake3Json "keyed_hash" fun key _ m d => blake3Keyed key m d, false⟩,
   ⟨file, id, .blake3Json "derive_key" fun _ c m d => blake3DeriveKey c m d, false⟩,
   ⟨file, id, .blake3Json "hash" fun _ _ m d => blake3Streamed blake3Init m d, true⟩,
   ⟨file, id, .blake3Json "keyed_hash" fun key _ m d =>
      blake3Streamed (blake3KeyedInit key) m d, true⟩,
   ⟨file, id, .blake3Json "derive_key" fun _ c m d =>
      blake3Streamed (blake3DeriveKeyInit c) m d, true⟩]

/-- circomlib's Poseidon, by the specification over `ZMod bn254` and by the fast
implementation over CompPoly's Montgomery representation. -/
def poseidonFiles : List TestFile :=
  let file := "poseidon/circomlib-bn254.json"
  [⟨file, id, .poseidonJson "reference" fun init ins nOut =>
      (ZK.Poseidon.Circom.poseidonEx ins.length (init : ZMod ZK.bn254)
        (fun i => (ins[i] : ZMod ZK.bn254)) nOut).map (·.val), false⟩,
   ⟨file, id, .poseidonJson "CompPoly" fun init ins nOut =>
      (HashZK.Poseidon.Circom.poseidonEx (init : HashZK.Poseidon.Circom.Fr)
        (ins.map fun x => (x : HashZK.Poseidon.Circom.Fr)).toArray nOut).map
        (HashZK.Poseidon.Circom.toZMod · |>.val), false⟩]

/-- A Plonky3 Poseidon2 instance by the specification over `ZMod p`. -/
def poseidon2Plonky3Ref (I : ZK.Poseidon2.Plonky3) (xs : List Nat) : List Nat :=
  (I.permutation (Vector.ofFn fun i => (xs.getD i.val 0 : ZMod I.p))).toList.map (·.val)

/-- Poseidon2 by the specification over `ZMod p`. -/
def poseidon2Ref (inst : String) (xs : List Nat) : Option (List Nat) :=
  match inst with
  | "plonky3-babybear-16" => some (poseidon2Plonky3Ref ZK.Poseidon2.babyBear16 xs)
  | "plonky3-babybear-24" => some (poseidon2Plonky3Ref ZK.Poseidon2.babyBear24 xs)
  | "plonky3-koalabear-16" => some (poseidon2Plonky3Ref ZK.Poseidon2.koalaBear16 xs)
  | "plonky3-koalabear-24" => some (poseidon2Plonky3Ref ZK.Poseidon2.koalaBear24 xs)
  | "horizenlabs-bn254-3" =>
    some ((ZK.Poseidon2.hlBn254Permutation
      (Vector.ofFn fun i => (xs.getD i.val 0 : ZMod ZK.bn254))).toList.map (·.val))
  | _ => none

/-- A BabyBear permutation on natural numbers, through CompPoly's representation. -/
def onBB {n : Nat} (f : Vector HashZK.Poseidon2.BB n → Vector HashZK.Poseidon2.BB n)
    (xs : List Nat) : List Nat :=
  (f (Vector.ofFn fun i => (xs.getD i.val 0 : HashZK.Poseidon2.BB))).toList.map
    fun x => (BabyBear.Fast.ringEquiv x).val

/-- A KoalaBear permutation on natural numbers, through CompPoly's representation. -/
def onKB {n : Nat} (f : Vector HashZK.Poseidon2.KB n → Vector HashZK.Poseidon2.KB n)
    (xs : List Nat) : List Nat :=
  (f (Vector.ofFn fun i => (xs.getD i.val 0 : HashZK.Poseidon2.KB))).toList.map
    fun x => (KoalaBear.Fast.ringEquiv x).val

/-- Poseidon2 by the fast implementation over CompPoly's Montgomery representations. -/
def poseidon2CompPoly (inst : String) (xs : List Nat) : Option (List Nat) :=
  match inst with
  | "plonky3-babybear-16" => some (onBB HashZK.Poseidon2.babyBear16 xs)
  | "plonky3-babybear-24" => some (onBB HashZK.Poseidon2.babyBear24 xs)
  | "plonky3-koalabear-16" => some (onKB HashZK.Poseidon2.koalaBear16 xs)
  | "plonky3-koalabear-24" => some (onKB HashZK.Poseidon2.koalaBear24 xs)
  | "horizenlabs-bn254-3" =>
    some ((HashZK.Poseidon2.hlBn254
      (Vector.ofFn fun i => (xs.getD i.val 0 : HashZK.Poseidon2.Fr))).toList.map
        fun x => (HashZK.Poseidon.Circom.toZMod x).val)
  | _ => none

/-- Poseidon2, by the specification and by the fast implementation. -/
def poseidon2Files : List TestFile :=
  [⟨"poseidon2/kats.json", id, .permutationJson "reference" poseidon2Ref, false⟩,
   ⟨"poseidon2/kats.json", id, .permutationJson "CompPoly" poseidon2CompPoly, false⟩]

/-- Every test file. -/
def testFiles : List TestFile :=
  shavs "SHA224" sha224 ++ shavs "SHA256" sha256 ++ shavs "SHA384" sha384 ++
  shavs "SHA512" sha512 ++ shavs "SHA512_224" sha512t224 ++ shavs "SHA512_256" sha512t256 ++
  shavsStreamed "SHA224" sha224Init ++ shavsStreamed "SHA256" sha256Init ++
  shavsStreamed "SHA384" sha384Init ++ shavsStreamed "SHA512" sha512Init ++
  shavsStreamed "SHA512_224" sha512t224Init ++ shavsStreamed "SHA512_256" sha512t256Init ++
  sha3vs "SHA3_224" sha3x224 ++ sha3vs "SHA3_256" sha3x256 ++ sha3vs "SHA3_384" sha3x384 ++
  sha3vs "SHA3_512" sha3x512 ++ shakevs "SHAKE128" shake128 ++ shakevs "SHAKE256" shake256 ++
  sha3vsStreamed "SHA3_224" sha3x224Init ++ sha3vsStreamed "SHA3_256" sha3x256Init ++
  sha3vsStreamed "SHA3_384" sha3x384Init ++ sha3vsStreamed "SHA3_512" sha3x512Init ++
  shakevsStreamed "SHAKE128" shake128Init ++ shakevsStreamed "SHAKE256" shake256Init ++
  [⟨"blake2/blake2-kat.json", id,
      .blake2Json "blake2b" fun key m nn => blake2bWith key .empty .empty nn m, false⟩,
   ⟨"blake2/blake2-kat.json", id,
      .blake2Json "blake2s" fun key m nn => blake2sWith key .empty .empty nn m, false⟩,
   ⟨"blake2/blake2-kat.json", id,
      .blake2Json "blake2b" fun key m nn => blake2Streamed (blake2bInit key .empty .empty nn) m,
      true⟩,
   ⟨"blake2/blake2-kat.json", id,
      .blake2Json "blake2s" fun key m nn => blake2Streamed (blake2sInit key .empty .empty nn) m,
      true⟩,
   ⟨"eip-152/vectors.txt", id, .eip152 blake2bPrecompile, false⟩] ++
  blake3Files ++ poseidonFiles ++ poseidon2Files

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
      | .blake2Json name f => runBlake2Json name f contents
      | .blake3Json mode f => runBlake3Json mode f contents
      -- EIP-152 vector 8 (2³² − 1 rounds) is skipped: too slow for a specification.
      | .eip152 f => runEip152 f 1000000 contents
      | .poseidonJson _ f => runPoseidonJson f contents
      | .permutationJson _ f => runPermutationJson f contents
    total := total + outcome.passed + outcome.failures.length
    failed := failed + outcome.failures.length
    let status := if outcome.failures.isEmpty then "ok" else "FAILED"
    let mode := match f.kind with
      | .blake2Json name _ | .blake3Json name _ | .poseidonJson name _
      | .permutationJson name _ =>
        if f.streaming then s!" ({name}, streamed)" else s!" ({name})"
      | _ => if f.streaming then " (streamed)" else ""
    let counts := s!"{outcome.passed} passed, {outcome.failures.length} failed"
    IO.println s!"{status}  {f.path}{mode}: {counts}"
    for e in outcome.failures.take 5 do
      IO.println s!"        {e}"
  if failed == 0 then
    IO.println s!"all {total} known-answer tests passed"
    return 0
  else
    IO.println s!"{failed} of {total} known-answer tests failed"
    return 1
