/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.TotalQuotientExponentStrictFloorBridge

/-!
# Certificate axiom audit for the strict floor-domination bridge

Covers both halves of the strict upgrade of
`TotalQuotientExponentStageAggregation.coarseFourFamilyFloor_le_fourFamilyExponent`:

* the strict level-two step of `MatrixMultiplication/TotalQuotientExponentLevelTwoStrictFloor.lean`
  — three exact rational comparisons against the committed directed branch floors, and the strict
  obligation they discharge; and
* the bridge itself,
  `TotalQuotientExponentStrictFloorBridge.coarseFourFamilyFloor_lt_fourFamilyExponent`, together
  with its copy-base form, which is what a `RetainedCountValid` client cites.

These assertions live in the opt-in certificate audit target because the declarations reach
`Generated/TotalQuotientExponentStageFloors.lean` and the generated level-two payload, exactly as
`AxiomAuditCertificate/TotalQuotientExponentLevelTwoGroupedCertificate.lean` does.

Build with

```text
lake build AxiomAuditCertificate
```

Each `#assert_axioms` fails elaboration if its declaration depends on any axiom other than
`propext`, `Classical.choice`, and `Quot.sound`.
-/

#assert_axioms MatrixMultiplication.TotalQuotientExponentLevelTwoStrictFloor.commonFloor_lt_branch0
#assert_axioms MatrixMultiplication.TotalQuotientExponentLevelTwoStrictFloor.commonFloor_lt_branch1
#assert_axioms MatrixMultiplication.TotalQuotientExponentLevelTwoStrictFloor.commonFloor_lt_branch2
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentLevelTwoStrictFloor.branchFloorCertified_of_strict
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentLevelTwoStrictFloor.branchFloorCertifiedStrict_of_normalizedForms
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentLevelTwoStrictFloor.levelTwoFamilyFloor_lt_familyExponent
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentLevelTwoStrictFloor.levelTwoFloor_lt_retainedExponent
#assert_axioms MatrixMultiplication.TotalQuotientExponentStrictFloorBridge.levelTwoFloor_lt_target
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentStrictFloorBridge.branchFloorCertifiedStrict
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentStrictFloorBridge.levelTwoFamilyFloor_lt_levelTwoFamilyExponent
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentStrictFloorBridge.coarseFourFamilyFloor_lt_fourFamilyExponent_of_levelTwoStrict
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentStrictFloorBridge.coarseFourFamilyFloor_lt_fourFamilyExponent
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentStrictFloorBridge.retainedCopyBase_lt_fourFamilyCopyBase
