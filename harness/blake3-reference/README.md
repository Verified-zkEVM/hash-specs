# Vendored BLAKE3 reference implementation

`src/lib.rs` is `reference_impl/reference_impl.rs` of <https://github.com/BLAKE3-team/BLAKE3> at
commit `f55849f89cd85083c1c9daa2c5de20766f309c00` (downloaded 2026-10-12), copied unmodified
(SHA-256 `6e89a18be72e3c4d838644e1796e04d896cb4a16bd7bb803d4380d7a363fbfd2`). It is released
into the public domain with CC0 1.0, or alternatively under Apache 2.0.

It is used only as a differential-testing oracle: a minimal, portable implementation that shares
no code with the optimised `blake3` crate.
