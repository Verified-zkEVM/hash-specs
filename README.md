# Hash Specifications

Lean4 specifications of hash functions

## Using it

The repository holds two Lake packages. Require the one you need, at a release tag: releases
are named after their Lean toolchain (`v4.35.0`, then `v4.35.0-patch1`, …; see
[Releases](https://github.com/Verified-zkEVM/hash-specs/releases)), and at a release tag Lake
downloads prebuilt oleans instead of compiling the library. Run `lake exe cache get` for Mathlib's
as usual.

**Core specifications** (`Hash`: SHA-2, SHA-3/Keccak, BLAKE2, BLAKE3, and Poseidon/Poseidon2 over
Mathlib's fields; depends only on Mathlib):

```toml
[[require]]
name = "hash-specs"
git = "https://github.com/Verified-zkEVM/hash-specs"
rev = "v4.34.0"
```

**ZK integration** (`HashZK`: Poseidon and Poseidon2 on CompPoly's fast field types; also brings
in the core package and CompPoly):

```toml
[[require]]
name = "hash-specs-zk"
git = "https://github.com/Verified-zkEVM/hash-specs"
rev = "v4.34.0"
subDir = "zk"
```

Each hash family is documented in the `README.md` of its directory under `Hash/`. See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for building and testing, and [`ROADMAP.md`](ROADMAP.md) for
the design.
