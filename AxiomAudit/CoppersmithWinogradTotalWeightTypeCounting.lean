/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightTypeCounting

/-! Focused trust audit for exact type counting in the total-weight CW quotient. -/

#assert_axioms
  AlgebraicComplexity.Examples.cwTotalWeight_card_conditionalTypeClass_le_entropyBase_pow
