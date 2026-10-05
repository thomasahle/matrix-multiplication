/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.TotalWeightEndpointComposition

/-!
# Certificate axiom audit for the `ω < 2.36999` final composition

Covers every public declaration of
`MatrixMultiplication/TotalWeightEndpointComposition.lean`, including the milestone's final
composition theorem `omega_lt_236999_final` — the theorem whose hypothesis list is the volume-only
milestone's residual — and the strict bridge's count-side client
`exists_retainedCountValid_of_fourFamilyCopyGrowth`.

These assertions live in the opt-in certificate audit target because the declarations reach
`Generated/TotalQuotientExponentStageFloors.lean` and the generated level-two payload through
`MatrixMultiplication/TotalQuotientExponentStrictFloorBridge.lean`, exactly as
`AxiomAuditCertificate/TotalQuotientExponentStrictFloorBridge.lean` does.

A conditional theorem is still fully audited: `#assert_axioms` recomputes the axiom cone of the
*proof*, so a hypothesis standing in for unfinished mathematics is visible in the statement and can
never be smuggled in as an axiom here.

Build with

```text
lake build AxiomAuditCertificate
```

Each `#assert_axioms` fails elaboration if its declaration depends on any axiom other than
`propext`, `Classical.choice`, and `Quot.sound`.
-/

#assert_axioms MatrixMultiplication.TotalWeightEndpointComposition.sourceLetters_eq
#assert_axioms MatrixMultiplication.TotalWeightEndpointComposition.sourceLetters_eq_304
#assert_axioms
  MatrixMultiplication.TotalWeightEndpointComposition.fourFamilyRetainedExponent
#assert_axioms
  MatrixMultiplication.TotalWeightEndpointComposition.coarseFourFamilyFloor_lt_fourFamilyRetainedExponent
#assert_axioms
  MatrixMultiplication.TotalWeightEndpointComposition.retainedFloor_le_fourFamilyRetainedExponent
#assert_axioms
  MatrixMultiplication.TotalWeightEndpointComposition.omega_lt_236999_of_eventualStageFamily
#assert_axioms MatrixMultiplication.TotalWeightEndpointComposition.omega_lt_236999_final
#assert_axioms
  MatrixMultiplication.TotalWeightEndpointComposition.exists_retainedCountValid_of_fourFamilyCopyGrowth
