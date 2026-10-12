# AI-tool use log

CSLib asks contributors to disclose AI-tool use in pull requests. This log records it for this
repository, so that the information is available if code is upstreamed (see `CONTRIBUTING.md`).

| Date | Tool | Scope | How it was used |
|---|---|---|---|
| 2026-10-11 | Claude Code (Claude Opus 5.5) | `LIT-REVIEW.md`, `ROADMAP.md` | Literature search and drafting, with multi-agent verification of claims; reviewed and edited by the maintainer. |
| 2026-10-11 | Claude Code (Claude Opus 5.5) | Phases 0–3: build setup, `Hash/`, `HashTests/`, `HashFFI/`, `HashKAT/`, `harness/`, `docs/`, CI | Wrote the specifications, proofs, tests, harness, book skeleton and CI, under the maintainer's direction. Specifications are checked against official test vectors and independent implementations, and proofs are kernel-checked. |
| 2026-10-12 | Claude Code (Claude Opus 5.5) | Phase 3: `Hash/BLAKE2/`, `Hash/BLAKE3/`, `Hash/Construction/Tree*`, tests, KATs, harness, chapters | Wrote the BLAKE2 and BLAKE3 specifications, the equivalence and streaming proofs, the known-answer tests, oracles and fuzz targets, and the two book chapters, under the maintainer's direction. |
