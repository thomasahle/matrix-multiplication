/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Census
import FixedPointTheorems.brouwer
import OAI.LinearAlgebra.MatrixMultiplication.AllFields
import OAI.LinearAlgebra.MatrixMultiplication.AllFieldsAudit
import OpenAIBridge.ArithmeticPrograms
import OpenAIBridge.Audit
import OpenAIBridge.Consequences
import OpenAIBridge.NineQuarters
import OpenAIBridge.Rectangular

/-!
# Bridge from the vendored `ω ≤ 9/4` proof to this repository, and its axiom census

Root of the opt-in `OpenAIBridge` target.  `ThirdParty/OAI/` vendors the Lean proof that the
matrix-multiplication exponent is at most `9/4` over every field (OpenAI's proof over `ℂ`, in the
all-fields form of `selanavot/matrix-multiplication-all-fields`), and OpenAI's proofs of two
rectangular bounds over `ℂ`; `ThirdParty/README.md` records sources, commits and licences.  The
modules imported here connect them to this repository's definitions:

* `OpenAIBridge/NineQuarters.lean`: `omega_le_nine_quarters : omega K ≤ 9 / 4` for every field
  `K`, a statement about `AlgebraicComplexity.omega`;
* `OpenAIBridge/Consequences.lean`: what that bound gives through machinery already here;
* `OpenAIBridge/ArithmeticPrograms.lean`: the vendored arithmetic-program exponents dominate
  this repository's rank-based ones over infinite fields;
* `OpenAIBridge/Rectangular.lean`: `ω(0.709) < 2.092` and `α > 0.465` for `rectangularOmega`
  and `rectangularAlpha`, over `ℂ` and over every field of characteristic zero;
* `OpenAIBridge/Audit.lean`: the enforcing `#assert_axioms` audit of the named theorems.

No module of `AlgebraicComplexity`, `MatrixMultiplication`, `AxiomAudit` or `Frontier` imports
this target or the vendored code.

## The census

`OpenAIBridge/Audit.lean` checks the theorems somebody chose to name.  The command at the end of
this file runs the environment walk of `AxiomAudit/Census.lean` over **every** declaration of the
vendored developments and of the bridge: all modules under the roots `OAI` and
`FixedPointTheorems` (`ThirdParty/`) and `OpenAIBridge`.  Elaboration fails if any of them
declares an axiom, or if any of their declarations — used by the headline theorem or not —
depends on an axiom outside `propext`, `Classical.choice` and `Quot.sound`.  In particular nothing
unproved and no `native_decide` can hide in a vendored lemma that the named assertions do not
reach.

The imports are the whole of the three targets: `AllFields`, `AllFieldsAudit` and the two
rectangular entry points imported by `OpenAIBridge/Rectangular.lean` between them import every
`OAI` module, `brouwer` every vendored `FixedPointTheorems` module, and the bridge modules are
named.  `scripts/check_source_coverage.sh` treats this file as the census
client of the `OpenAIBridge` target.

These roots are not in `AxiomAudit.projectModuleRoots`, and `AxiomAudit/CensusAll.lean` does not
import them: the ordinary census stays independent of vendored code.
-/

#axiom_census_roots OAI FixedPointTheorems OpenAIBridge
