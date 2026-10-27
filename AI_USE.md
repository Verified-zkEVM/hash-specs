# AI-tool use log

CSLib asks contributors to disclose AI-tool use in pull requests. This log records it for this
repository, so that the information is available if code is upstreamed (see `CONTRIBUTING.md`).

| Date | Tool | Scope | How it was used |
|---|---|---|---|
| 2026-10-11 | Claude Code (Claude Opus 5.5) | `LIT-REVIEW.md`, `ROADMAP.md` | Literature search and drafting, with multi-agent verification of claims; reviewed and edited by the maintainer. |
| 2026-10-11 | Claude Code (Claude Opus 5.5) | Phases 0–3: build setup, `Hash/`, `HashTests/`, `HashFFI/`, `HashKAT/`, `harness/`, `docs/`, CI | Wrote the specifications, proofs, tests, harness, book skeleton and CI, under the maintainer's direction. Specifications are checked against official test vectors and independent implementations, and proofs are kernel-checked. |
| 2026-10-12 | Claude Code (Claude Opus 5.5) | Phase 3: `Hash/BLAKE2/`, `Hash/BLAKE3/`, `Hash/Construction/Tree*`, tests, KATs, harness, chapters | Wrote the BLAKE2 and BLAKE3 specifications, the equivalence and streaming proofs, the known-answer tests, oracles and fuzz targets, and the two book chapters, under the maintainer's direction. |
| 2026-10-12 | Claude Code (Claude Opus 5.5) | `Hash/*/StreamLemmas.lean`, `Hash/*/README.md`, CI fixes | Wrote the streaming-equals-one-shot proofs for SHA-2, Keccak and BLAKE2, the per-family reference READMEs, and fixes for Linux linking, runner disk and memory, and `lake lint`. |
| 2026-10-12 | Claude Code (Claude Opus 5.5) | Phase 4: `Hash/ZK/`, `Hash/Construction/FieldSponge*`, `HashZK/`, `HashFFI/Poseidon*`, `HashKAT/vectors/poseidon*`, harness, chapters, `docs/research/` | Researched the Poseidon and Poseidon2 instances (research notes with provenance in `docs/research/`), and wrote the specifications, the Grain constant derivation, the equivalence proofs across field representations, the field sponges, the known-answer tests, oracles, fuzz targets and the two book chapters, under the maintainer's direction. |
| 2026-10-27 | Claude Code (Claude Opus 5.5) | Docs: `Hash/*/README.md`, `Hash/ZK/Poseidon*/README.md`, `docs/`, `ROADMAP.md`, `CONTRIBUTING.md`, CI | Removed the Verso book and its dependency; folded its assurance tables and diagrams into the per-family READMEs, and wrote the Poseidon and Poseidon2 READMEs from the book chapters, under the maintainer's direction. |
