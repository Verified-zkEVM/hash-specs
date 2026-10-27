# Evidence for the upstreaming records

The scratch files behind the records in `docs/upstreaming/`, kept so their claims can be
re-checked. They are **not** part of any Lake library, and are not built in CI.

- **What they contain.** Most contain verbatim copies of definitions from the repo they concern,
  pinned to the commit named in that repo's record. The copied code keeps its licence: `clean`
  and `evm-asm` are MIT, `VCVio`, `ArkLib`, `leanerVM` and `machine-checked` are Apache-2.0, and
  `zkLean` is BSD-3-Clause. riscv-zkvm's `ZiskAccel` definitions, inside `evm-asm/`, are under
  riscv-zkvm's licence.
- **What they check.** Each copy is followed by differential checks or bridge proofs against
  hash-specs at `98c225d` (`v4.35.0-patch1`).

Run them from the repository root, which uses the core package's build:

```
lake build Hash
lake env lean --run docs/upstreaming/evidence/<repo>/<File>.lean   # files with a `main`
lake env lean docs/upstreaming/evidence/<repo>/<File>.lean         # proof-only files
```

The `arklib/` files use CompPoly, so run them from `zk/` (after `lake build` there), with the
path adjusted to `../docs/upstreaming/evidence/arklib/...`.

| Directory | Contents |
|---|---|
| `clean/` | Keccak-f bridge (`KeccakBridge.lean`, proved); Keccak absorb bug, SHA-256, BLAKE3, Poseidon checks |
| `vcvio/` | SHA-2/SHA-3/SHAKE differential and KAT runs, compression and permutation equality, size lemmas, benchmark |
| `evm-asm/` | ZisK accelerator and SpecRef differential checks (`Check.lean`); unfinished BLAKE2b round bridge (`Proof.lean`, has a `sorry`); axiom check |
| `leanervm-machine-checked/` | BLAKE2s and BLAKE2b differential checks |
| `arklib/` | Poseidon2 KoalaBear: ArkLib's permutation, the pre-0.6 constant order, bridge sketch, kernel constant checks |
| `zklean/` | Keccak-f bridge (`Bridge.lean`, proved), SHA3-256 differential check |
