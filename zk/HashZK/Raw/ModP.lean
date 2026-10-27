/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.ZK.Common.FieldOps

/-!
# Small prime fields on natural numbers

The operations of `ZMod p` on natural numbers, reducing modulo `p` after every operation, for the
C exports of `HashFFI` over the 31-bit fields (BabyBear, KoalaBear). The values stay below `2⁶²`,
so the runtime computes on machine words. The inverse is `x ^ (p − 2)`, by square-and-multiply.
The module does not import Mathlib; `HashZK.Raw.ModP.hom_toZMod` proves that the map to `ZMod p`
preserves the operations when `p` is prime.
-/

@[expose] public section

namespace HashZK.Raw

open Hash.ZK

/-- An element of `ℤ/pℤ`, represented by a natural number. -/
structure ModP (p : Nat) where
  /-- The representative. -/
  val : Nat

namespace ModP

variable {p : Nat}

/-- The operations without the inverse, from which the inverse is computed. -/
@[instance_reducible] def baseOps (p : Nat) : FieldOps (ModP p) where
  zero := ⟨0⟩
  one := ⟨1 % p⟩
  add x y := ⟨(x.val + y.val) % p⟩
  neg x := ⟨(p - x.val % p) % p⟩
  mul x y := ⟨(x.val % p) * (y.val % p) % p⟩
  ofNat n := ⟨n % p⟩
  inv x := x

instance : FieldOps (ModP p) :=
  { baseOps p with inv := fun x => @FieldOps.pow (ModP p) (baseOps p) x (p - 2) }

end ModP

end HashZK.Raw
