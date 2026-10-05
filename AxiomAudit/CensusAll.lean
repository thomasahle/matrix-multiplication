/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Census
import AxiomAudit.CensusRoots
import AxiomAudit.RawCyclicRowExtractionCensus
import AxiomAudit
import AxiomAudit.DuanWuZhouLevelTwo
import AlgebraicComplexity
import AlgebraicComplexity.DuanWuZhouLevelTwo
import AlgebraicComplexityClients
import MatrixMultiplication
import Frontier

/-!
# Enforcing axiom census for the ordinary build targets

This module runs `#axiom_census` (see `AxiomAudit/Census.lean`) over the whole ordinary import
closure: the reusable library, the client umbrella, the paper library, and the focused audit root.
Elaboration fails if any module of this repository declares an `axiom`, or if any project
declaration depends on an axiom outside `propext`, `Classical.choice`, and `Quot.sound`.

Why the imports are what they are: the census can only see modules it imports, so its scope must
equal the build's scope.  The three public umbrellas plus the audit root cover every ordinary
target, and `Frontier` — the leaderboard's statement anchor — is a deliberate leaf that no
library
imports, so it has to be named here explicitly; `AlgebraicComplexity.DuanWuZhouLevelTwo` — the
level-two tier's own `[[lean_lib]]` target, which no other umbrella imports — is the same case.
`AxiomAudit.DuanWuZhouLevelTwo` is the same case again on the audit side: it is a build root
through the `globs = ["AxiomAudit.*"]` entry, but no module imports it, so without this line
the tier's `#assert_axioms` companions sit inside the build and outside every census closure.
`AxiomAudit.CensusRoots` closes the remaining gap: modules that are built only because a focused
`#assert_axioms` audit imports them sit inside the build but outside every umbrella, and that
generated manifest imports their maximal elements.
`scripts/check_source_coverage.sh` enforces that equality, so a module added to a target but not to
a census closure is a build failure rather than a silent hole.  The opt-in
generated-certificate cone is covered separately by
`AxiomAuditCertificate/Census.lean`.

Unlike the `#assert_axioms` lists, nothing here needs maintenance when a theorem is added: the
census walks `Environment.constants` and therefore covers declarations nobody remembered to name.
It is the authority for the trust policy in `DESIGN.md`; `scripts/trust_scan.sh` is a fast
pre-filter whose line-anchored regex a mid-line `axiom` can evade.

```text
lake build AxiomAudit.CensusAll
```
-/

#axiom_census
