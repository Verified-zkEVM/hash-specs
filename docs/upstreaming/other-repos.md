# Upstreaming record: remaining Verified-zkEVM repos

This is a sweep for hash code in the org repos that have no record of their own, read 2026-10-27.
Clones were shallow clones of HEAD (not kept). The search was a case-insensitive
grep for `keccak|sha-?256|sha2|sha3|blake|poseidon|ripemd|hash` over all files, then a manual
reading of each hit. Bare `hash` hits for `Hashable`, `HashMap` and `HashSet` were discarded.

| Repo | SHA | Toolchain | Verdict |
|---|---|---|---|
| leanth | `6eab3f9` (2026-08-10) | v4.28.0 | **Opportunity.** Poseidon v1, KoalaBear t=16 (planned; open PR #18) |
| verified-zkevm.org | `c1acc15` (2026-10-10) | v4.29.0 | **Opportunity.** List hash-specs on the site |
| hax | `4a7adf2` (2026-06-04) | v4.29.0-rc1 (Lean lib) | Small, optional: a `lean_sha256` example |
| rust-lean | `49a83d2` (2026-04-18) | v4.22.0–v4.29.0-rc1 | Hash is abstract; optional instance later |
| Overview | `755c9d6` (2025-07-19) | n/a (README only) | Stale; optional one-line mention |
| PolyFun | `b13c074` (2026-10-26) | v4.35.0 | No hash code; nothing to do (by policy) |
| loom2 | `682151a` (2026-04-19) | `master` (sic) | No hash code; nothing to do |
| iris-lean | `e53cf76` (2026-05-19) | v4.28.0 | No hash code; nothing to do |

## leanth

The biggest opportunity in this sweep. leanth formalizes leanVM, which is hash-based, and on `main`
it has **no hash code yet**. There are only 8 Lean files, all of them scaffold or tests. Hash code is
planned, and an implementation is open:

- **Plan.** Packet `agent/packets/M2/m2-05-poseidon-sponge.md:5–12` targets
  `Leanth.Poseidon.permute`. It is 16-wide KoalaBear, x^3 S-box, 4+20+4 rounds, circulant MDS first
  row `[1,3,13,22,67,…]`, and constants "as shipped in leanVM-rs". It also targets `compress`
  (feed-forward) and `Leanth.Sponge.hash`. `docs/research/clusters/02-fields-poseidon.md:69–93`
  establishes that this is **Poseidon v1, not Poseidon2** (`poseidon1_koalabear_16.rs`).
- **Implementation.** Open PR **#18** "Poseidon Circuit + FlatAIR Implementation" (scaraven, opened
  2026-08-12, last updated 2026-08-12) adds the following in `Leanth/Poseidon/Dense.lean`:
  - `State := Vector Fp 16`, with `Fp := KoalaBear.Field` from CompPoly
  - `sbox x := x*x*x`
  - `mdsEntry i j := mdsCol[(16+i−j)%16]`
  - `mix s := ofFn fun i => ∑ j, mdsEntry i j * s[j]`
  - `fullRound c s := mix (sbox ∘ ark c s)`
  - `partialRound` (ARK on the whole row, S-box on element 0, then mix)
  - `permute`, as three `List.finRange` folds of 4, 20 and 4 rounds
  - `compress s := (permute s + s)[0:8]`

  It also adds a `Sparse.lean` variant with `Equivalence.lean`, and Clean circuits.

  This is **exactly** our `Hash.ZK.Poseidon.Reference.round`: ARC, then S-box on all elements or on
  element 0, then `M.mulVec` (`Hash/ZK/Poseidon/Reference.lean:63–72`).

**Bridge** (proposed, not attempted):

```lean
def leanVMParams : Hash.ZK.Poseidon.Params Fp 16 :=
  ⟨3, 8, 20, fun r i => (rc ⟨r % 28, _⟩)[i], Matrix.of mdsEntry⟩

theorem permute_eq (s) :
    Leanth.Poseidon.permute s = Hash.ZK.Poseidon.Reference.permutation leanVMParams s
```

Difficulty: structural and small. It needs `pow_three`/`sbox` (ours is `x ^ α`,
`Hash/ZK/Common/Sbox.lean:38`), `Matrix.mulVec` versus `∑`, and the split of one 28-round fold
into 4/20/4.

**Gap in hash-specs.** We have Poseidon v1 only for circomlib BN254 (and Poseidon2 for Plonky3
KoalaBear). We should add a `Poseidon.LeanVM.KoalaBear.t16` instance, with constants from
`poseidon1_koalabear_16.rs`, and a differential test against leanVM-rs. `ROADMAP.md:338` already
notes that leanSpec moved to Poseidon1 over KoalaBear, which is very likely the same instance
(**unverified**).

**Toolchain.** v4.28.0 → v4.35.0. leanth also pins Clean, CompPoly, VCVio and ArkLib by commit
(`lakefile.toml`), so a bump moves four dependencies.

**Recommendation.** Talk to the PR #18 author before it merges. Either leanth adopts
`Hash.ZK.Poseidon.Reference.permutation` as its dense spec, or it keeps `Dense.lean` and adds
`permute_eq`. Either way, we add the leanVM instance first.

## verified-zkevm.org

`verified-zkevm/Data.lean` is the site's data file, not a tracker of hash work. Its hash mentions
are:

- a Fiat-Shamir/duplex-sponge grant (l.404–405)
- a talk "Comparing ZK Constraints – Keccak, Plonky3" (l.813)
- the Formal Land article "Formal verification of the Keccak precompile from Plonky3" (l.878–879)

None of these is a spec to replace. It also holds the **Repositories list** (`kind := .repo`,
l.987–1063 and on). That list names `Verified-zkEVM/ArkLib`, `CompPoly`, `VCVio`, `clean`,
`zkLean`, `PolyFun`, `rust-lean` and others, but **not hash-specs**. The cryptography track
overview (l.79–84) describes "three related libraries" (ArkLib, VCV-io, CompPoly). The
opportunity is a small PR that adds a `kind := .repo` entry:

```lean
{ kind := .repo, title := "Verified-zkEVM/hash-specs"
  url := "https://github.com/Verified-zkEVM/hash-specs"
  blurb? := some "Executable, formally specified hash functions (SHA-2, SHA-3/Keccak, BLAKE2/3, Poseidon, Poseidon2)"
  trackTags := [.cryptography] }
```

The PR could also add a sentence to the cryptography overview. The commit style is short
imperatives ("Add reviewed repository links to grants"). Two PRs are open (#6 and #7, content PRs
from 2026-01), and neither touches the repo list. Size XS. Do it once hash-specs is public and
tagged.

## hax

There are **no Lean hash proof libraries or models.** The Lean proof library
`hax-lib/proof-libs/lean` (Qq only, no Mathlib) has `core_models.hash.{Hasher,Hash}`
(`Hax/core_models/core_models.lean:445–459`). That is Rust's `std::hash` trait, not a
cryptographic hash. The other matches are not Lean:

- `examples/sha256/src/sha256.rs`, a 183-line SHA-256, extracted only to F* and Coq
  (`proofs/{fstar,coq}/extraction/`)
- ProVerif crypto abstractions (`hax-lib-protocol/src/crypto.rs`,
  `engine/names/src/crypto_abstractions.rs`, `tests/proverif-noise/*`, `examples/proverif-psk`)
- generated identifier tables, lockfiles and nix files

There is no Rust Keccak in the tree.

The opportunity is optional and medium-sized: a new `examples/lean_sha256` (alongside
`lean_chacha20` and `lean_barrett`). It would extract `sha256.rs` with `cargo hax into lean`, and
prove

```lean
Sha256.hash m = Hash.sha256 m
```

The hash-specs `require` would go only in that example's lakefile, because the Hax library must
stay Mathlib-free. Blockers:

- The Lean examples are on v4.29.0-rc1 (every `examples/lean_*/proofs/lean/lean-toolchain`).
- The VzE repo is a fork of `pereq-dev/hax`. Upstream `cryspen/hax` is very active (pushed
  2026-10-27), so the PR belongs there, and Mathlib in an example may be unwelcome. Ask first.

This would be a strong demonstration ("Rust SHA-256 verified against a FIPS spec"), not
deduplication.

## rust-lean

Hax- and Aeneas-to-Lean case studies. `hax-merkle` verifies RISC Zero's Merkle root
recomputation, but the hash is a **parameter**:

- `rust/merkle_root_rs/src/lib.rs:13` has `struct Digest(pub [u32; 8])`, and l.19 has
  `hash_pair: fn(&Digest, &Digest) -> Digest`.
- The extracted Lean (`lean/MerkleRootLean/Extracted/Merkle_root_rs.lean:61–102`) keeps it
  abstract, and `Proof.lean` proves properties for any `hash_pair`.

There is no hash code to replace. An optional later step is a concrete instance with RISC Zero's
SHA-256 `hash_pair` (**unverified** whether that is full SHA-256 of the 64-byte concatenation or a
raw compression call; check `risc0/zkvm/src/sha`). Its `Digest` is `[u32; 8]`, which needs a
words↔bytes adapter. The toolchains are spread across v4.22.0 (`hax-merkle`), v4.23.0, v4.26.0,
v4.28.0 and v4.29.0-rc1, so any adoption needs a bump per sub-project. The other sub-projects
(FRI, Horner, adc, Plonky3 fields) have no hashes. Low priority.

## Overview

`Verified-zkEVM/Overview` is a 39-line README with links to repositories, last pushed 2025-07-19.
Its "Cryptography Track" section (l.27–37) names ArkLib, VCV-io and hax. It has no hash content.
It is stale and has been superseded by verified-zkevm.org. An optional XS PR could add a hash-specs
link there, but updating the site (above) matters more.

## PolyFun

No hash code; nothing to do. Its policy excludes it explicitly: `docs/development/
troubleshooting.md:24–31` says "Do not introduce dependencies on … concrete cryptographic algebra
(specific groups, fields, hash functions) … Cryptographic content belongs in VCVio". It is already
on v4.35.0. Open PR #366 (cryptol import) matched the search only on generic terms. None of
its changed file paths mentions a hash; its contents were not read.

## loom2

No hash code; nothing to do. The only hits are `Hashable SpecProof` and `PHashSet`
(`Loom/Tactic/Attr.lean:49–50,106`). Its `lean-toolchain` contains the literal string `master`,
which is not a valid release pin.

## iris-lean

No hash code; nothing to do. The only hit is `Std.HashSet` (`src/Iris/ProofMode/
SynthInstance.lean:39`). This is the Bluebell/Iris fork on v4.28.0.
