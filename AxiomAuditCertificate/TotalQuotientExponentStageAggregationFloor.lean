/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.TotalQuotientExponentStageAggregation

/-!
# Certificate axiom audit for the stage-floor transfer of the total-weight track

`TotalQuotientExponentStageAggregation.coarseFourFamilyFloor_le_fourFamilyExponent`
carries the four certified per-stage floors of the `e7987` total-weight candidate across to the
four-family retained exponent at the *committed stage-floor sum* `8.241973`, rather than at the
`C′` acceptance split `411/50` the module's other transfers use.  It is the retained bound
`MatrixMultiplication/SimplifiedSequencePackaging.lean` composes at, since its `retainedFloor` is
definitionally the same `Generated/TotalQuotientExponentStageFloors` constant.

The assertion lives in the opt-in certificate audit target rather than the ordinary focused one
because the declaration reaches `Generated/TotalQuotientExponentStageFloors.lean`, exactly as for
`AxiomAuditCertificate/SimplifiedSequencePackaging.lean`.  The module's remaining declarations —
the two shape identifications and the three acceptance-split transfers — are asserted from
`AxiomAudit.lean`, which does not reach generated data through them.

Build with

```text
lake build AxiomAuditCertificate
```

The assertion fails elaboration if the declaration depends on any axiom other than `propext`,
`Classical.choice`, and `Quot.sound`.
-/

#assert_axioms
  MatrixMultiplication.TotalQuotientExponentStageAggregation.coarseFourFamilyFloor_le_fourFamilyExponent
