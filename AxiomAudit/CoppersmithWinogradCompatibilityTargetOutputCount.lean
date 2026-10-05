/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetOutputCount

/-!
# Trust audit for explicit repaired CW compatibility-target outputs

This focused audit covers the asymptotic-growth wrapper around the natural-valued output count.
The finite arithmetic and semantic stage have their own lighter audit module.
-/

#assert_axioms
  AlgebraicComplexity.Examples.natCast_cwProportionalFullCellTypeSelectionLossNat
#assert_axioms AlgebraicComplexity.Examples.natCast_cwProportionalTargetRepairBudgetNat
#assert_axioms AlgebraicComplexity.Examples.natCast_four_mul_cwFixedTypeTargetLosses
#assert_axioms
  AlgebraicComplexity.Examples.cwFixedTypeTargetOutputQuotientLoss_subexponential
#assert_axioms AlgebraicComplexity.Examples.cwFixedTypeTargetOutput_combinedLoss_subexponential
#assert_axioms
  AlgebraicComplexity.Examples.familyCard_lt_two_mul_cwTargetLosses_mul_fixedTypeCount_add_one
#assert_axioms
  AlgebraicComplexity.Examples.natCast_familyCard_le_cwFixedTypeTargetOutputQuotientLoss_mul_count
#assert_axioms
  AlgebraicComplexity.Examples.pow_le_ambientLoss_mul_cwFixedTypeTargetOutputQuotientLoss_mul_count
