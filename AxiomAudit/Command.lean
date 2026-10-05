/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Lean.Elab.Command

/-!
# The `#assert_axioms` command

`#assert_axioms id` recomputes the axioms that `id` depends on, exactly as `#print axioms`
does, and fails elaboration unless every one of them belongs to the standard allowlist
(`propext`, `Classical.choice`, `Quot.sound`).  A module of such asserts is an enforced
regression test rather than output a human must read: an introduced `sorry`, a project axiom,
or `native_decide` (via `Lean.ofReduceBool`/`Lean.trustCompiler`) in the audited dependency
cone fails the build.
-/

namespace AxiomAudit

open Lean Elab Command

/-- Axioms an audited declaration may depend on: the three standard classical principles. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- `#assert_axioms id` fails elaboration unless every axiom `id` depends on is one of
`propext`, `Classical.choice`, and `Quot.sound`. -/
elab "#assert_axioms " id:ident : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  for name in names do
    let axioms ← liftCoreM <| collectAxioms name
    let bad := axioms.filter fun ax => !allowedAxioms.contains ax
    unless bad.isEmpty do
      throwError "'{name}' depends on non-allowlisted axioms: {bad.toList}"

end AxiomAudit
