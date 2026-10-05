/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SimplifiedExponentCompatibilityBranchProjection

/-! Axiom audit for the generic weighted compatibility-branch projections. -/

#assert_axioms MatrixMultiplication.SimplifiedExponentRecursiveConstituent.weightedFamilyBranchRate_one_eq_logicalY_sum
#assert_axioms MatrixMultiplication.SimplifiedExponentRecursiveConstituent.weightedFamilyBranchRate_two_eq_logicalZ_sum
