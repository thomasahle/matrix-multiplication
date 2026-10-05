/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetOutputCore

/-! Trust audit for the finite repaired-output count and supply inequalities. -/

#assert_axioms AlgebraicComplexity.Examples.cwProportionalTargetRepairBudgetNat_pos
#assert_axioms
  AlgebraicComplexity.Examples.cwFixedTypeTargetRepairOutputCount_pos_of_fits
#assert_axioms AlgebraicComplexity.Examples.cwOutput_clog_add_two_three_pow_mul_le
#assert_axioms
  AlgebraicComplexity.Examples.cwOutput_logarithmicRepairDepth_le_three_mul_width
#assert_axioms
  AlgebraicComplexity.Examples.cwSevenBranchTargetRepairBudget_le_proportional
#assert_axioms
  AlgebraicComplexity.Examples.two_mul_cwFixedTypeTargetRepairOutputCount_mul_sevenBranchBudget_le_fixed
#assert_axioms
  AlgebraicComplexity.Examples.cwFixedTypeTargetRepairOutputCount_mul_sevenBranchBudget_le_sparse_of_half
