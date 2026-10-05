/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightDivisionLeafStage

/-! Focused trust audit for the nested total-weight exact division leaf. -/

#assert_axioms
  AlgebraicComplexity.Examples.cwTotalWeightLocalizedOuter_wholeStage_of_fixedCoarseType
#assert_axioms
  AlgebraicComplexity.Examples.cwTotalWeightLocalizedOuter_fixedCoarseTypeDivisionLeafStage
