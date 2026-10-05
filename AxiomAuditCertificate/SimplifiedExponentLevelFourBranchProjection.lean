/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SimplifiedExponentLevelFourBranchProjection

/-! Axiom audit for the compatibility-branch projections of the level-four recurrence. -/

#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.branchRateOnParentsFrom_one_eq_logicalY_sum
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.branchRateOnParentsFrom_two_eq_logicalZ_sum
