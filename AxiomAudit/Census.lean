/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command

/-!
# The `#axiom_census` command

`#assert_axioms` (see `AxiomAudit/Command.lean`) checks the declarations a human remembered to
name.  `#axiom_census` checks the *environment*: it walks every constant whose originating module
belongs to this repository and fails elaboration when either

1. the constant is itself a declared `axiom` — no project module may postulate anything; or
2. the constant depends on an axiom outside the allowlist
   (`propext`, `Classical.choice`, `Quot.sound`), which also catches `sorryAx`,
   `Lean.ofReduceBool`/`Lean.trustCompiler` (`native_decide`), and any axiom a dependency
   introduces later.

## Why this exists

`scripts/trust_scan.sh` greps for `axiom` in declaration position, i.e. anchored at the start of a
line.  That is a fast pre-filter, not a decision procedure: Lean's command parser is
whitespace-insensitive, so both

```text
/-- innocent docstring -/ axiom sneaky : False
theorem harmless : True := trivial axiom sneaky : False
```

elaborate as an ordinary axiom declaration while starting their line with something else.  A
regex over source text can always be evaded this way; a walk over `Environment.constants` cannot,
because it inspects what the kernel actually accepted.  **The census is the authority for the
trust policy; the grep is only the fast pre-filter.**

## Scope

A census only covers what its module imports, so the guarantee is exactly "no project module in
this import closure postulates or uses anything outside the allowlist".  The enforcing clients
therefore import the public umbrellas: `AxiomAudit/CensusAll.lean` for the ordinary targets and
`AxiomAuditCertificate/Census.lean` for the opt-in generated-certificate target.  Both are built
by CI.

## Cost

Since Lean 4.23 the axiom dependencies of an *imported* declaration are precomputed when its
olean is written (`Lean.exportedAxiomsExt`), so `collectAxioms` is a binary search rather than a
term walk.  The census therefore costs one pass over the constant table plus one lookup per
project declaration; the expensive part of running it is loading the umbrella oleans, which the
build pays anyway.
-/

namespace AxiomAudit

open Lean Elab Command

/-- Module-name roots owned by this repository.  A constant is "ours" exactly when its
originating module lies under one of these; everything else is Lean core, Mathlib, or CSLib. -/
def projectModuleRoots : List Name :=
  [`AlgebraicComplexity, `AlgebraicComplexityClients, `MatrixMultiplication,
    `MatrixMultiplicationCertificate, `AxiomAudit, `AxiomAuditCertificate]

/-- Whether `mod` is a module of this repository, i.e. `projectModuleRoots` contains it or one of
its prefixes. -/
def isProjectModule (mod : Name) : Bool :=
  projectModuleRoots.any fun root => root == mod || root.isPrefixOf mod

/-- How many offending declarations a failing census names before summarizing the rest.  The list
is a debugging aid: the failure itself does not depend on the cut-off. -/
private def reportLimit : Nat := 20

private def formatCulprits (culprits : Array MessageData) : MessageData :=
  let shown := culprits.extract 0 (min culprits.size reportLimit)
  let body := MessageData.joinSep shown.toList (MessageData.ofFormat Format.line)
  if culprits.size ≤ reportLimit then body
  else body ++ m!"\n… and {culprits.size - reportLimit} more."

/--
`#axiom_census` fails elaboration if any module of this repository in the current import closure
declares an axiom, or if any of its declarations depends on an axiom outside `propext`,
`Classical.choice`, and `Quot.sound`.  On success it reports the audited scope and the axioms
actually used, so a build log records what was checked rather than only that something passed.
-/
elab "#axiom_census" : command => do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let projectModule : Array Bool := moduleNames.map isProjectModule
  let projectModuleCount : Nat :=
    projectModule.foldl (fun (count : Nat) (isProject : Bool) =>
      if isProject then count + 1 else count) 0
  -- Every constant whose home module is ours, paired with that module.  Imported constants carry
  -- their module in `const2ModIdx`; the declarations of the module being elaborated right now do
  -- not appear there, so they are collected from the environment's local stage.  Without that
  -- second source an `axiom` written into the census client itself would go unseen.
  let mut targets : Array (Name × Name) := #[]
  for (declName, modIdx) in env.const2ModIdx do
    let idx := modIdx.toNat
    if idx < moduleNames.size && projectModule[idx]! then
      targets := targets.push (declName, moduleNames[idx]!)
  if isProjectModule env.mainModule then
    targets := env.constants.foldStage2 (fun acc declName _ =>
      acc.push (declName, env.mainModule)) targets
  let mut scanned : Nat := 0
  let mut declaredAxioms : Array MessageData := #[]
  let mut tainted : Array MessageData := #[]
  let mut usedAxioms : NameSet := {}
  for (declName, moduleName) in targets do
    -- `const2ModIdx` also maps compiler-generated auxiliary names that have no `ConstantInfo`.
    let some info := env.find? declName | continue
    scanned := scanned + 1
    match info with
    | .axiomInfo _ =>
      declaredAxioms := declaredAxioms.push m!"{declName} (declared in {moduleName})"
    | _ =>
      let axioms ← liftCoreM <| collectAxioms declName
      for ax in axioms do
        usedAxioms := usedAxioms.insert ax
      let bad := axioms.filter fun ax => !allowedAxioms.contains ax
      unless bad.isEmpty do
        tainted := tainted.push m!"{declName} ({moduleName}) uses {bad.toList}"
  unless declaredAxioms.isEmpty do
    throwError "axiom census: {declaredAxioms.size} axiom(s) are declared in project modules. \
      Committed project sources must postulate nothing.\n{formatCulprits declaredAxioms}"
  unless tainted.isEmpty do
    throwError "axiom census: {tainted.size} project declaration(s) depend on non-allowlisted \
      axioms.\n{formatCulprits tainted}"
  logInfo m!"axiom census clean: {scanned} declarations in {projectModuleCount} project modules \
    (of {moduleNames.size} imported modules); no project axiom is declared, and the only axioms \
    reached are {usedAxioms.toList}."

end AxiomAudit
