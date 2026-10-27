# Upstreaming record: zkLean

Scope: `examples/zkLeanExamples/Sha3/{Spec,Circuit,Proof}/*`. The zkLean library itself (`zkLean/`,
`bvmod_eq/`) has no hash code. The only hit for "hash" there is the `Hashable` superclass of
`ZKField` and `Std.HashMap` (`zkLean/zkLean/Semantics.lean:12,19`).

**Bottom line.** The SHA3 code is an *example*, not a library. Nothing outside
`zkLeanExamples` imports it, and its four binary-operation gadgets are still `sorry`. Adopting
hash-specs therefore buys a showcase, not deduplication across the org: "a zkLean circuit, proved
against a spec that is proved equal to FIPS 202". The spec agrees with hash-specs. I proved the
permutation-level bridge (`keccakF_bridge`, below) against our v4.35.0 build, with no `sorry` and
no warnings, and SHA3-256 agrees on 1800 messages. The blocker is the toolchain: zkLean is on
v4.25.2, ten minor releases behind, and its proofs sit on `Std.Do`. **Priority: low.** It is worth
doing when upstream bumps its toolchain anyway.

## 1. Snapshot

| Item | Value |
|---|---|
| Repo examined | `Verified-zkEVM/zkLean`, HEAD `eb17e50` (2026-03-10, "Fix typo in README.md"), read 2026-10-27 |
| Actual upstream | `GaloisInc/zkLean`, HEAD `014fa39` (2026-05-04). The VzE copy is **not** a GitHub fork (`parent: null`). It has diverged: VzE has `eb17e50`, which GaloisInc lacks, and GaloisInc has `b7fb630` and `014fa39` (case-sensitivity fixes, touching `examples/zkLeanExamples.lean` and `bvmod_eq/…/RangeAnalysis.lean`), which VzE lacks. Every PR so far (#3–#15) was made on GaloisInc. |
| Activity | VzE: last push 2026-03-10, no PRs, no issues. GaloisInc: last merge 2026-05-04, and open PR #16 (bvmod_eq CAV integration) was last updated 2026-05-15. **About 5 months quiet.** It is dormant rather than dead. |
| Toolchain | `leanprover/lean4:v4.25.2`, the same in `lean-toolchain`, `examples/lean-toolchain`, `zkLean/lean-toolchain` and `bvmod_eq/lean-toolchain` |
| Pins | `zkLean/lakefile.toml`: mathlib `v4.25.2`, cslib `v4.25.1` ("they did not make a 4.25.2 release yet"), and BVModEq (path). `bvmod_eq/lakefile.toml`: mathlib `v4.25.2`. `examples/lakefile.toml`: BVModEq and zkLean (paths only). The manifest pins mathlib `c98ae54`. |
| Lakefile format | `.toml` everywhere. The root `lakefile.toml` is a convenience aggregator. |
| Module system | **No.** There is no `module` header in any file. |
| CI / CONTRIBUTING / CODEOWNERS | None. There is no `.github/` directory. |
| Toolchain gap | v4.25.2 → v4.35.0 (10 minor releases) |

**Does adoption force a toolchain bump? Yes.** A `require` at another toolchain does not work in
Lake, and the example would have two Mathlib pins, `v4.25.2` from zkLean and `v4.35.0` from
hash-specs. Two options:

- *Bump zkLean to v4.35.0.* The dependencies exist: Mathlib `v4.35.0`, and cslib tag `v4.35.0`
  (checked with `gh api repos/leanprover/cslib/tags`). The risk is `Std.Do`, which this work rests
  on. `zkLean/zkLean/Formalism.lean` uses `PredTrans.pushArg`/`pushOption` (l.45, l.84) and the
  `Cslib.FreeM` API (l.1–2, l.14–15, l.67). The SHA3 proofs use `mspec`, `mintro`, `mpure`,
  `Invariant` and `Spec.foldlM_array` (`Proof.lean:26–77`). Std.Do changed between these releases.
  For example, hax carries shims in `hax-lib/proof-libs/lean/Hax/MissingLean/Std/Do/*` at
  v4.29.0-rc1. **Unverified how much breaks.** A previous attempt, GaloisInc PR #12 "Draft: Bump
  Lean version to 4.28.0-rc1" (protoben), has been a stale draft since 2026-02-10. It touches only
  toolchains, manifests, lakefiles and `bvmod_eq/BVModEq/SolveMLE.lean`. Estimate: **M–L**, most of
  it in `bvmod_eq` and `Formalism`, not in SHA3.
- *Cut a hash-specs release at v4.25.2.* Not realistic. It would mean backporting the whole
  library, which uses the module system and is built against Mathlib v4.35.0, across ten releases.
  Not recommended.

Checked: `Spec.lean` is self-contained (it has no imports), and it compiles unchanged on v4.35.0
(it is non-module, and a non-module file can import our `module` files) with **0 warnings**. The
part of the bump that touches the spec is free.

## 2. Overlap inventory

All of these are in `examples/zkLeanExamples/Sha3/Spec.lean` (namespace `SHA3`). The representation
is `BitVec 64` lanes in a `Vector … 25`, with lane `(x, y)` at index `5y + x`, the same indexing as
ours.

| Line | Name : signature | Representation | hash-specs counterpart |
|---|---|---|---|
| 8–16 | `roundConstants : Array (BitVec 64)` | BitVec 64 | `Hash.Keccak.roundConstants : List Nat` (`Hash/Keccak/Constants.lean:40`), and `Hash.Keccak.Fast.roundConstantWords : Array UInt64` (`Fast.lean:70`) |
| 19–21 | `rotationOffsets : Array Nat` (**unused** anywhere) | Nat, mod 64 | `Hash.Keccak.rhoOffsets` (`Constants.lean:31`, not reduced mod 64), and `Fast.rhoRotations` (`Fast.lean:49`). All 25 values agree mod 64 (checked by hand). |
| 24–26 | `structure State where lanes : Vector (BitVec 64) 25` | Vector of BitVec | `Array UInt64` (the Fast layer), and `Hash.Keccak.State 64 = Fin 5 → Fin 5 → Fin 64 → Bool` (`KeccakP.lean:32`) |
| 29–38 | `State.init`, `State.get (x y : Fin 5)`, `State.set` | | `Fast.lane a i = a.getD i 0` (`Fast.lean:32`), and `Array.replicate 25 0` |
| 41–50 | `theta : State → State` | | `Fast.theta : Array UInt64 → Array UInt64` (`Fast.lean:41`) |
| 52–80 | `rho_pi : State → State` (ρ and π fused, unrolled) | | `Fast.pi ∘ Fast.rho` (`Fast.lean:52,56`) |
| 83–111 | `chi : State → State` (unrolled) | | `Fast.chi` (`Fast.lean:63`) |
| 114–116 | `iota : State → Fin 24 → State` | | `Fast.iota : Array UInt64 → Nat → Array UInt64` (`Fast.lean:73`) |
| 119–120 | `keccakRound : State → Fin 24 → State` | | `Fast.round` (`Fast.lean:77`) |
| 123–124 | `keccakF : State → State` (an `Array.finRange 24` foldl) | | `Fast.keccakF` (`Fast.lean:81`, a `List.range 24` foldl), and `Hash.Keccak.keccakF 6` / `keccakP 6 24` on `List Bool` (`KeccakP.lean:143,149`) |
| 127–135 | `loadLittleEndian : ByteArray → Nat → BitVec 64` | `++` of bytes | `ByteArray.getUInt64LE` (`Hash/Prelude/Bytes.lean`) |
| 138–147 | `absorb : State → ByteArray → Nat → State` (block extracted, lanes with `8i < rate`, then keccakF) | | `Fast.absorbBlock rate a p off` (`Fast.lean:94`) |
| 150–165 | `pad101 : ByteArray → Nat → ByteArray` (domain byte fixed at `0x06`) | | `Fast.pad rate 0x06` (`Fast.lean:87`) |
| 167–174 | `squeeze : State → ByteArray` (first 32 bytes only) | | `(Fast.squeeze 136 a 1 .empty).extract 0 32` (`Fast.lean:104`) |
| 177–187 | `sha3_256 : ByteArray → ByteArray` | ByteArray | **`Hash.sha3x256`** (`Hash/Keccak/API.lean:31`) |
| 190–197 | `ByteArray.toHex` | | no counterpart in the public API; this is a test utility |
| 205–282 | `SHA3.Tests.*`, 3 vectors; `#eval runAllTests` at l.285 | | the empty-string vector is already a kernel-checked test in `HashTests/Keccak.lean:29`. All three pass against `Hash.sha3x256` (see §7). |

Circuit-side duplicates, which are not specs: `Circuit/Iota.lean:5–13` `roundConstants : Array
(ZKExpr f)` repeats the 24 constants as field literals. They are tied to the spec by
`roundConstants_eqF` (`Proof/Iota.lean:23–28`, by `decide`).

There is nothing for Poseidon, SHA-2, BLAKE or Keccak-256. The example covers SHA3-256 only.

## 3. How it is used

Nothing outside `examples/zkLeanExamples/Sha3/` and the aggregator `examples/zkLeanExamples.lean`
imports `Sha3.Spec`. Outside `Spec.lean` there are 31 `SHA3.`/`Sha3.Spec` references, in 9 files.

**Target of correctness proofs.** These are the permutation only, `SHA3.State` and the step
functions:

| File | References | What |
|---|---|---|
| `Proof.lean` | 14 | `keccakRound.soundness` (l.21–33) and `keccakF.soundness` (l.68–77): the postcondition `eqState s1 (SHA3.keccakF s0_bv)` (l.71). The invariant is at l.40–43, `list_foldl_eq_array_foldl` at l.63–66. |
| `Proof/Theta.lean` | 7 | `theta.soundness` (l.261–), plus helpers over `SHA3.State.get` (l.122, l.231) |
| `Proof/RhoPi.lean` | 3 | `rho_pi.soundness` (l.21–24), `simp only [SHA3.rho_pi, eqF]` (l.259) |
| `Proof/Chi.lean` | 3 | `chi.soundness` (l.14–17), `simp only [SHA3.chi, eqF]` (l.276) |
| `Proof/Iota.lean` | 8 | `iota.soundness` (l.51–), `roundConstants_eqF` (l.23), `eqState_set` (l.30) |
| `Circuit/State.lean` | 2 | `eqState (s : State) (sBV : SHA3.State) : Bool` (l.82–83), the circuit↔spec relation |
| `Proof/{And,Not,Xor,Shift}.lean` | 1 each (import) | gadget specs over raw `BitVec 64`; all four are `sorry` (e.g. `Proof/Xor.lean:15`) |

The proofs unfold the spec definitions syntactically, for example `unfold theta SHA3.theta`
(`Proof/Theta.lean:267`) and `simp only [SHA3.chi …]`. They depend on the *unrolled
`Vector (BitVec 64) 25` shape*, which matches the circuit's `Vector (ZKExpr f) 25`
(`Circuit/State.lean:37–38`). Re-targeting them at `Hash.Keccak.Fast` directly (`Array UInt64`,
`tabulate`, `getD`) would mean rewriting about 970 lines of proof (Theta 347, RhoPi 264, Chi 281,
Iota 78). **Do not do that.** Keep `SHA3.State` as the circuit-facing spec and bridge it.

**Executable only.** `absorb`, `pad101`, `squeeze`, `loadLittleEndian` and `sha3_256` are used
only by the spec's own tests (`Spec.lean:239,250,261`). Nothing proves anything about them, so they
can be swapped for `Hash.sha3x256` directly. `rotationOffsets` is dead code.

## 4. Representation gaps and adapter lemmas

There is one adapter, `SHA3.State ↔ Array UInt64`. It is trivial because both sides use the
`5y + x` index and 64-bit lanes:

```lean
def toLanes (s : SHA3.State) : Array UInt64 := s.lanes.toArray.map UInt64.ofBitVec
theorem size_toLanes (s) : (toLanes s).size = 25
theorem lane_toLanes (s) (i) (h : i < 25) : Hash.Keccak.Fast.lane (toLanes s) i = UInt64.ofBitVec s.lanes[i]
theorem getElem_toLanes (s) (i) (h : i < (toLanes s).size) :
    (toLanes s)[i] = UInt64.ofBitVec (s.lanes[i]'(by simpa [toLanes] using h))
```

All of these are proved, by `simp`.

**Who should provide it.** The repo should, since `SHA3.State` is its own type. hash-specs could
optionally provide a generic `Vector (BitVec 64) 25 ↔ Array UInt64` view. Several downstream
specs use `Vector`/`BitVec` lanes, so it would be reusable, but it is not needed here.

## 5. Bridge theorems (proved)

These were proved in a scratch file against hash-specs HEAD `98c225d` on v4.35.0. The file is
`Spec.lean` lines 1–199 verbatim, plus the following. It ran with
`lake env lean evidence/zklean/Bridge.lean` and gave no errors, no warnings and no `sorry`, in
about 11 s. It needs `import Hash` and `import Std.Tactic.BVDecide` (the latter is now unused and
can be dropped).

```lean
open Hash.Keccak.Fast
theorem theta_bridge  (s) : toLanes (SHA3.theta s)  = theta (toLanes s)
theorem rho_pi_bridge (s) : toLanes (SHA3.rho_pi s) = pi (rho (toLanes s))
theorem chi_bridge    (s) : toLanes (SHA3.chi s)    = chi (toLanes s)
theorem iota_bridge   (s) (r : Fin 24) : toLanes (SHA3.iota s r) = iota (toLanes s) r.val
theorem round_bridge  (s) (r : Fin 24) : toLanes (SHA3.keccakRound s r) = round (toLanes s) r.val
theorem keccakF_bridge (s : SHA3.State) :
    toLanes (SHA3.keccakF s) = Hash.Keccak.Fast.keccakF (toLanes s)
/-- …and therefore Keccak-p[1600,24] of FIPS 202, via our `Equiv.keccakP_toString`. -/
theorem keccakF_reference (s : SHA3.State) :
    (Hash.Keccak.Equiv.toState (toLanes (SHA3.keccakF s))).toString =
      Hash.Keccak.keccakP 6 24 (Hash.Keccak.Equiv.toState (toLanes s)).toString
```

The proof pattern is `Array.ext`, then `interval_cases i` over the 25 lanes, then `simp` with the
step definitions. ρ and θ need `apply UInt64.toBitVec_inj.mp; simp [Hash.UInt64.rotl,
BitVec.rotateLeft_def, BitVec.ushiftRight_eq_zero]` (`rotl x 0 = x` needs `x >>> 64 = 0`). `iota`
needs `fin_cases r`. `keccakF_bridge` folds `round_bridge` over the list; it needs
`(Array.finRange 24).toList.map Fin.val = List.range 24` (by `decide`). Difficulty: **structural,
done**. The full proof is saved at
`evidence/zklean/Bridge.lean`.

Composing with the circuit. `keccakF.soundness` (`Proof.lean:68`) gives `eqState s1
(SHA3.keccakF s0_bv)`. Together with `keccakF_bridge`, the circuit output's lanes are
`Hash.Keccak.Fast.keccakF (toLanes s0_bv)`. A packaged Hoare-triple corollary is optional, and its
exact form under Std.Do on v4.35 is **unverified**:

```lean
theorem keccakF.soundness_hashSpecs (s0 : State) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄ keccakF s0
  ⦃ ⇓? s1 _e => ⌜∃ t : SHA3.State, eqState s1 t ∧
        toLanes t = Hash.Keccak.Fast.keccakF (toLanes s0_bv)⌝ ⦄
```

There is also the byte-level bridge, **not proved**:

```lean
theorem SHA3.sha3_256_eq (m : ByteArray) : SHA3.sha3_256 m = Hash.sha3x256 m
```

It holds on every message tested (§7). Proving it is a structural proof of medium size. It needs:

- `pad101 m 136 = Fast.pad 136 0x06 m`, by cases on `q = 1`
- `loadLittleEndian b o = (b.getUInt64LE o).toBitVec`
- absorbing the extracted block versus absorbing at an offset
- `squeeze` on 32 bytes versus `rateBytes` followed by `extract 0 32`

Its value is low, because no proof consumes `sha3_256`. The simpler move is to delete it (PR 3).

## 6. Gaps in hash-specs

None block this. Optional additions:

- A `Vector (BitVec 64) 25` view of `Fast.keccakF`, or the generic adapter in §4. It would save
  downstream repos the 25-way `interval_cases` boilerplate.
- `Fast.round` takes the round index as `Nat` (`Fast.lean:77`), and so does `Fast.iota`
  (`Fast.lean:73`), which is `getD`-guarded. zkLean uses `Fin 24`, and the bridge passes `r.val`.
  That works fine, so no change is needed.

## 7. Discrepancies

None found. These checks were run in hash-specs with
`lake env lean --run evidence/zklean/Check.lean`:

- **Permutation and rounds.** `toLanes (SHA3.keccakF s) = Fast.keccakF (toLanes s)`, and the
  same for `keccakRound`/`round` for all 24 `r`, on 50 pseudo-random states: 0 mismatches. This is
  now also a theorem (§5).
- **SHA3-256.** `SHA3.sha3_256 m = Hash.sha3x256 m` for every length 0–599 with 3 byte patterns,
  1800 messages in all: 0 mismatches. This covers the `padLen = 1` branch (`0x86`,
  `Spec.lean:156–157`) at lengths ≡ 135 (mod 136), and multi-block messages.
- **Vendored vectors** (`Spec.lean:225–234`). `Hash.sha3x256` gives
  - `a7ffc6f8…8434a` for `""`
  - `3a985da7…1431532` for `"abc"`
  - `79f38ade…e31787` for 200×`0xa3`

  All three match.
- **Constants.** `rotationOffsets` matches `rhoOffsets mod 64` entry by entry. The round constants
  match (`iota_bridge` checks all 24 by `simp`).

Latent fragility in the zkLean spec, which does not affect SHA3-256:

- `absorb` (`Spec.lean:142`) XORs a lane whenever `8i < rate`. The correct check, `8i + 8 ≤ rate`,
  is commented out at l.141. A rate that is not a multiple of 8 would read past the block, and `b[…]!`
  would default to 0.
- `squeeze` (`Spec.lean:167–174`) hard-codes 32 output bytes, and `pad101` hard-codes the SHA-3
  domain byte `0x06`.

So the spec is SHA3-256 only. It is not a general sponge.

Other notes:

- `Spec.lean:285` has a top-level `#eval SHA3.Tests.runAllTests`, which runs on every build.
  `#guard` would be better.
- `Circuit/State.lean:19` has `ScalarField_is_prime := sorry` (BN254), and l.25 has a `sorry` in
  `field_to_bits`.

These are unrelated to hashes, but they mean the end-to-end statement is conditional anyway.

## 8. PR plan

**Target `GaloisInc/zkLean`**, not the VzE copy. Then sync `Verified-zkEVM/zkLean`, which has
diverged and has no PR history. The conventions are informal: commit titles are short imperatives
("Fix AssertLTE", "Rename Keccak to Sha3", "Docs"), and PR titles are sentences ("Generalize number
of bits for `lookup_mle`"). There is no CI, CONTRIBUTING or CODEOWNERS. Merges have been done by
Valentin Robert, and James Parker (JP) is the SHA3 author. Commits authored by `claude` were merged
for this very example (e.g. `626de54` "Chi proven", `011a37f`), so AI-assisted work is accepted.
There is no disclosure policy, but say so in the PR body anyway. Open PRs that touch the same area:
#12 (toolchain bump, stale draft) and #16 (bvmod_eq CAV integration, touches `examples/*` but not
`Sha3/`).

**Prerequisites in hash-specs: none.** The release `v4.35.0-patch1` already has everything used
here.

**PR 0 (optional, in hash-specs, no dependency on zkLean).** `Spec.lean` has no imports, so a
pinned copy of `Spec.lean` (lines 1–199) plus `Bridge.lean` could live in a hash-specs test or
bridge directory, as a "compat" check. That is evidence that needs no toolchain bump. It is not
circular, because it copies their spec and does not import their package. It is the maintainer's
call whether to vendor third-party specs.

1. **"Bump Lean to v4.35.0"** (in practice, revive or replace #12).
   - Files: the 4 `lean-toolchain` files, `zkLean/lakefile.toml` (mathlib `v4.35.0`, cslib
     `v4.35.0`, dropping the l.18 comment), `bvmod_eq/lakefile.toml`, and the 3
     `lake-manifest.json`.
   - Proof fixes go in `bvmod_eq/*`, `zkLean/zkLean/Formalism.lean` and possibly
     `Sha3/Proof/*.lean` (Std.Do churn).
   - Size: **M–L, unverified**.
   - Risks: Std.Do API drift, a `bvmod_eq` conflict with #16 (land #16 first), and the build time
     of `AssertLTE` ("~6 minutes", `examples/zkLeanExamples.lean:2`).
2. **"Prove the SHA3 example spec equal to hash-specs"**.
   - `examples/lakefile.toml` gets:
     ```toml
     [[require]]
     name = "hash-specs"
     git = "https://github.com/Verified-zkEVM/hash-specs"
     rev = "v4.35.0-patch1"
     ```
     Only the examples package needs it. The `zkLean` core library stays free of the dependency.
   - New file `examples/zkLeanExamples/Sha3/HashSpecs.lean`: `toLanes`, the 4 adapter lemmas, the
     6 step and permutation bridges, and `keccakF_reference`. This is the scratch proof, about
     90 lines.
   - Add an import to `examples/zkLeanExamples.lean`, and a README paragraph (after l.33).
   - Nothing is deleted, and no proof needs rework.
   - Size: **S**.
   - Risks: Mathlib resolution. The root manifest must take hash-specs' Mathlib, which equals
     zkLean's after PR 1. hash-specs' prebuilt oleans should be used.
3. **"Use hash-specs for SHA3-256 hashing in the example"** (optional).
   - In `Sha3/Spec.lean`, delete `loadLittleEndian`, `absorb`, `pad101`, `squeeze`, `sha3_256` and
     the unused `rotationOffsets` (l.19–21, 126–187). Point the tests at `Hash.sha3x256`, or delete
     them, since hash-specs has KATs. Replace `#eval` with `#guard`.
   - Keep `State`, `theta`…`keccakF` and `roundConstants`, because the circuit proofs target them.
   - Size: **S**, about −70 lines.
   - Risk: none, since nothing proves anything about these functions.
4. *(optional)* **"State keccakF soundness against hash-specs"**: the Hoare corollary in §5.
   Size: **S**, once its Std.Do form is checked.

## 9. Open questions for the maintainers

1. Which repo is canonical, GaloisInc or Verified-zkEVM? Should VzE become a real fork or be
   synced?
2. Is a toolchain bump planned (#12 was a draft for v4.28.0-rc1)? Would you accept v4.35.0
   directly?
3. Should the example take on a Mathlib-heavy dependency just for a bridge? The alternative is PR 0
   on our side.
4. Will the gadget circuits and proofs for `xor64`/`and64`/`not64`/`rotateLeft64`, which are
   currently `sorry` and "in another fork" (README l.34), land? Without them the end-to-end claim is
   conditional, whatever spec it targets.
5. Is a Keccak-256 (EVM, `ds = 0x01`) variant of the example of interest? The bridge would be the
   same `keccakF_bridge`, plus `Hash.keccak256`.
