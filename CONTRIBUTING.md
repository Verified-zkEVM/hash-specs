# Contributing to `Hash`

`Hash` is a library of formal, executable specifications of hash functions in Lean 4. This
document is the style guide for specifications, proofs, tests and documentation. The plan and its
rationale are in [`ROADMAP.md`](ROADMAP.md).

## Building and testing

| Task | Command |
|---|---|
| Fetch Mathlib's cache (after cloning or updating) | `lake exe cache get` |
| Build the library (warnings are errors in CI) | `lake build --wfail Hash` |
| Kernel-checked tests and the axiom audit | `lake build --wfail HashTests` |
| Environment linters | `lake lint` |
| Layering and hygiene checks | `python3 scripts/check_layers.py` |
| Full known-answer test suites | `lake exe hash-kat` |
| Differential tests against other implementations | `cd harness/hash-lean && cargo test --release` |
| Fuzzing (one target) | `cd harness/fuzz && cargo +nightly fuzz run sha2` |
| Benchmarks (a record only, see `harness/BENCHMARKS.md`) | `cd harness/hash-lean && cargo bench`, then `python3 harness/scripts/bench_report.py` |
| The book | `lake exe hash-docs --output _site`, then open `_site/html-multi/index.html` |
| Rebuild the diagrams | `docs/diagrams/build.sh` (needs TeX Live and `pdftocairo`) |
| Build Layer 1 on CSLib's pins (advisory) | `scripts/cslib_compat.sh` |

The toolchain is pinned to CompPoly's (`lean-toolchain`). Keep the build at **zero warnings**.

## Layers

The repository is one Lake package with three layers of libraries (ROADMAP.md §2.1):

1. **Core specifications**: `Hash` and `HashTests`. These depend on Mathlib at most, and
   follow CSLib's conventions so that they could be upstreamed. `scripts/check_layers.py` checks
   that Layer 1 imports nothing else.
2. **ZK integration**: `HashZK`, which may also use CompPoly.
3. **Tooling**: `HashFFI` (C exports), `HashKAT` (full test suites), `harness/` (Rust),
   `docs/` (the Verso book).

Within Layer 1, files that do not need Mathlib must not import it. This includes the prelude, and
the reference and fast specifications of the byte-oriented hashes. That keeps the C-export library
small and keeps a Mathlib-free core splittable. Proof files that need Mathlib import `Hash.Init`,
which mirrors `Cslib.Init`.

## Writing a specification

Each hash has the same set of files under `Hash/<Family>/`:

| File | Contents |
|---|---|
| `Constants.lean` | Constant tables as printed in the standard, each proved equal to its definition. |
| `Reference.lean` | The **reference** specification: the standard transcribed line by line. |
| `Fast.lean` | The **fast** specification: the same algorithm on machine words and byte arrays. |
| `Instances.lean` | The members of the family, as parameter sets. |
| `API.lean` | Byte-array functions, computed by the fast specification. |
| `Equiv.lean` | The theorem that the fast specification equals the reference. |

### Reference specifications

- **Use the standard's names, indexing and data model.** For example, FIPS 180-4 works with bit
  strings and `w`-bit words, so `Hash.SHA2.Reference` uses `List Bool` and `BitVec w`. A reader
  should be able to hold the PDF next to the Lean file.
- **Cite the section on every definition**, as `[FIPS 180-4, §6.2.2]`, and list the standard in
  the module docstring's `## References`.
- **Parameterise where the standard does**, for example over the members of a family.
- Clarity over speed: the reference only has to run on small inputs.

### Fast specifications

- Same structure as the reference, step by step, on `UInt32`/`UInt64`, `Array` and `ByteArray`.
  The closer the structure, the easier the equivalence proof.
- Must handle multi-megabyte inputs in reasonable time. It is not meant to compete with optimised
  libraries; `harness/BENCHMARKS.md` records how it compares.

### Constants are theorems, not trusted data

Nothing-up-my-sleeve constants are written as tables (so auditors can compare them with the
standard) and proved equal to their definitions by kernel computation, for example
`Hash.SHA2.K256_eq`. Kernel-friendly helpers are in `Hash/Prelude/Arith.lean`.

### Instance names

"Poseidon" and similar names are ambiguous. Name instances by ecosystem and parameters, for
example `Poseidon.Circom.BN254.t3`, and record where the parameters come from: paper table,
reference repository and commit, and generation script.

## Proofs and the axiom policy

- **No `sorry`, `admit`, `native_decide` or `axiom` anywhere in Layer 1**, tests included. Use
  `decide +kernel` for computation. `scripts/check_layers.py` checks this textually, and every
  public theorem is listed in `HashTests/Axioms.lean` with `audit_axioms`. That fails the build
  unless the theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
- Follow Mathlib style and CSLib's `CODESTYLE.md`: prefer term-mode `def`s, keep proofs readable,
  use `simp only` rather than non-terminal `simp`, and avoid large terminal `simpa` calls.
- Treat curated `simp`/`grind` sets as part of the API.

## Tests

- **`HashTests/`** (Layer 1): a small representative set of known answers, checked with
  `decide +kernel`, so they are proofs and could go upstream with the library.
- **`HashKAT/`** (Layer 3): the full official suites (NIST CAVP and the designers' vectors),
  vendored under `HashKAT/vectors/` with a provenance and licence record for each file.
- **`harness/`** (Layer 3): property tests and coverage-guided fuzzing against at least two
  independent implementations per hash. Any divergence becomes a regression test, plus an issue
  recording which side was wrong according to the standard.

## Documentation

- Every declaration has a docstring. Module docstrings explain the file and give references.
- The book (`docs/`) has one chapter per hash, following the template in ROADMAP.md §3. Code
  in the book is elaborated against the library.
- Diagrams are original TikZ in `docs/diagrams/`, compiled to SVG in `docs/static/` with
  `docs/diagrams/build.sh`. Use the shared style (`style.tex`), never copy figures from papers,
  and commit both the `.tex` source and the `.svg`.
- Every source goes in `references.bib`, with a DOI or stable URL.

## AI-assisted contributions

CSLib requires pull requests to disclose AI-tool use. So that contributions from this repository
can be upstreamed, record AI-tool use in [`AI_USE.md`](AI_USE.md): which tool, and what it was
used for.

## Commits

Commit messages start with a type: `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`,
`perf`, `build` or `ci`, optionally followed by a scope, as in `feat(SHA2): …`.
