/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

/-!
# Axiom audit

`audit_axioms c₁ c₂ …` fails unless every listed constant depends only on the three standard
axioms `propext`, `Classical.choice` and `Quot.sound`. In particular it rejects proofs that use
`sorry` (`sorryAx`) or `native_decide` (`Lean.ofReduceBool`, `Lean.trustCompiler`). This enforces
the axiom policy of ROADMAP.md §2.3 in the build itself.
-/

public meta section

open Lean Elab Command

namespace HashTests

/-- The axioms a Layer 1 theorem may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `audit_axioms c₁ c₂ …` checks that each `cᵢ` depends only on the standard axioms. -/
syntax (name := auditAxioms) "audit_axioms" (ppSpace ident)+ : command

/-- Elaborate `audit_axioms`: collect each constant's axioms and fail on any outside
`allowedAxioms`. -/
@[command_elab auditAxioms]
def elabAuditAxioms : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axioms ← liftCoreM <| collectAxioms name
    let bad := axioms.toList.filter (· ∉ allowedAxioms)
    unless bad.isEmpty do
      throwErrorAt id m!"`{name}` depends on disallowed axioms: {bad}"

end HashTests
