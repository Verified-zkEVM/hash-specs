/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.SHA2.API

/-!
# C entry points for the differential-testing harness

Each function takes and returns a `ByteArray` and is exported under a stable C symbol name, so
that the Rust harness in `harness/` can call the fast specifications in-process. This library
must stay Mathlib-free: it is linked into the harness as a static library together with Lean's
runtime, and importing Mathlib would make that library enormous.

Arguments are owned (exported functions cannot take borrowed parameters), so the caller passes
one reference to the input, which the callee consumes.
-/

public section

namespace HashFFI

/-- SHA-224. -/
@[export hs_sha224] def sha224 (m : ByteArray) : ByteArray := Hash.sha224 m
/-- SHA-256. -/
@[export hs_sha256] def sha256 (m : ByteArray) : ByteArray := Hash.sha256 m
/-- SHA-384. -/
@[export hs_sha384] def sha384 (m : ByteArray) : ByteArray := Hash.sha384 m
/-- SHA-512. -/
@[export hs_sha512] def sha512 (m : ByteArray) : ByteArray := Hash.sha512 m
/-- SHA-512/224. -/
@[export hs_sha512t224] def sha512t224 (m : ByteArray) : ByteArray := Hash.sha512t224 m
/-- SHA-512/256. -/
@[export hs_sha512t256] def sha512t256 (m : ByteArray) : ByteArray := Hash.sha512t256 m

end HashFFI
