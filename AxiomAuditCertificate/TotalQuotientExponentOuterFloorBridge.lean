/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.TotalQuotientExponentOuterFloorBridge

/-!
# Certificate axiom audit for the root and level-three outer floor seam

Covers every public declaration of
`MatrixMultiplication/TotalQuotientExponentOuterFloorBridge.lean`, including the two bridge-shaped
domination theorems `rootFloor_le_rootBranchRate` and `levelThreeFloor_le_branchRate` that a
producer's certificates turn into the `hroot` / `hlevelThree` hypotheses of
`MatrixMultiplication.TotalWeightEndpointComposition.omega_lt_236999_final`.

These assertions live in the opt-in certificate audit target because the declarations reach the
generated stage floors of `Generated/TotalQuotientExponentStageFloors.lean`, exactly as
`AxiomAuditCertificate/TotalQuotientExponentStrictFloorBridge.lean` does.

A conditional theorem is still fully audited: `#assert_axioms` recomputes the axiom cone of the
*proof*, so a parameter standing in for an unlanded producer payload is visible in the statement
and can never be smuggled in as an axiom here.

Build with

```text
lake build AxiomAuditCertificate
```

Each `#assert_axioms` fails elaboration if its declaration depends on any axiom other than
`propext`, `Classical.choice`, and `Quot.sound`.
-/

#assert_axioms
  MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.BranchFloorCertificate
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.BranchFloorCertificate.floor_le_rate
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.BranchFloorCertificate.ofEmpty
#assert_axioms MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.rootFloor_eq_zero_two
#assert_axioms MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.rootFloor_eq_zero_three
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.floor_le_rate_of_branchCertificates
#assert_axioms MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.rootRateOfRows
#assert_axioms MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.rootBranchBits
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.rootBranchCertificateOfForms
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.rootFloor_le_rootBranchRate
#assert_axioms MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.totalQuotientRootRate
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.rootFloor_le_totalQuotientRootRate
#assert_axioms MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.levelThreeBits
#assert_axioms MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.levelThreeRate
#assert_axioms MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.repeatedXZYOrder
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.repeatedXZYOrder_isPermutation
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.levelThreeBranchCertificateOfForms
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentOuterFloorBridge.levelThreeFloor_le_branchRate
