/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

import HashTests.Audit
import Hash

/-!
# Axiom audit of the library's theorems

Every theorem of Layer 1 that a downstream user may rely on is listed here. The build fails if any
of them depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`.
-/

-- SHA-2 constants [FIPS 180-4, §4.2, §5.3].
audit_axioms Hash.SHA2.K256_eq Hash.SHA2.K512_eq Hash.SHA2.initialHash256_eq
  Hash.SHA2.initialHash512_eq Hash.SHA2.initialHash384_eq Hash.SHA2.initialHash224_eq
  Hash.SHA2.initialHash512t224_eq Hash.SHA2.initialHash512t256_eq

-- SHA-2: the fast specification equals the reference [FIPS 180-4].
audit_axioms Hash.SHA2.Equiv.hashWith_eq Hash.SHA2.sha224_eq Hash.SHA2.sha256_eq
  Hash.SHA2.sha384_eq Hash.SHA2.sha512_eq Hash.SHA2.sha512t224_eq Hash.SHA2.sha512t256_eq
