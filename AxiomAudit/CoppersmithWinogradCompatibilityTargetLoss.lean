/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetLoss

/-! Enforcing audit for candidate-independent CW compatibility-target losses. -/

#assert_axioms AlgebraicComplexity.Examples.cwTargetRepairBudgetLoss_subexponential
#assert_axioms
  AlgebraicComplexity.Examples.cwProportionalFullCellTypeSelectionLoss_subexponential
#assert_axioms AlgebraicComplexity.Examples.cwProportionalTargetRepairLoss_subexponential
