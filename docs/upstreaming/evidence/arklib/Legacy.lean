import HashZK
open Hash.ZK Hash.ZK.Poseidon2 FieldOps
/-- Pre-0.6 Plonky3 / leanSpec draw order: initial external, final external, internal. -/
def legacySamples (I : Plonky3) : List Nat × List Nat :=
  match Grain.sampleList I.p 31 (8 * I.t) (Grain.init ⟨1, 0, 31, I.t, 8, I.RP⟩) with
  | (e, s) => match Grain.sampleList I.p 31 I.RP s with
    | (i, _) => (e, i)
def legacyFast (I : Plonky3) (F : Type) [FieldOps F] : Fast.Params F I.t :=
  let (ce, ci) := legacySamples I
  { I.fastParams F with CE := (ce.map fun c => (ofNat c : F)).toArray,
                        CI := (ci.map fun c => (ofNat c : F)).toArray }
abbrev KB := HashZK.Poseidon2.KB
def run (I : Plonky3) (xs : List Nat) : List Nat :=
  (Fast.permutation (legacyFast I KB) (Vector.ofFn fun i => (xs.getD i.val 0 : KB))).toList.map
    fun x => (KoalaBear.Fast.ringEquiv x).val
def main : IO Unit := do
  IO.println (run koalaBear16 [894848333, 1437655012, 1200606629, 1690012884, 71131202,
  1749206695, 1717947831, 120589055, 19776022, 42382981, 1831865506, 724844064, 171220207,
  1299207443, 227047920, 1783754913])
  IO.println (run koalaBear16 (List.replicate 16 0))
  IO.println (run koalaBear24 (List.range 24))
