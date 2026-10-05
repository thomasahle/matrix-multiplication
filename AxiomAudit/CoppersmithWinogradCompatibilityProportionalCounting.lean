/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityProportionalCounting
import AxiomAudit.Command

/-! Enforcing axiom audit for proportional CW compatibility counting. -/

open AlgebraicComplexity.Examples

#assert_axioms CWCompatibilityCleanupData.coarseKept_card_le_proportionalLoss_mul_sparse_of_incidence
#assert_axioms CWCompatibilityCleanupData.fixedTargetCellType_card_le_two_mul_sparse_of_incidence
#assert_axioms card_cwExactTargetSubalphabet_le_proportional_three_pow
