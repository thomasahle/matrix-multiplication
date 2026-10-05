/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightIsolatedSupport

/-! Focused trust audit for lossless total-weight compatibility cleanup. -/

#assert_axioms
  AlgebraicComplexity.Examples.cwTotalWeightYIsolatedSupport_eq_ambient_of_injOn
#assert_axioms
  AlgebraicComplexity.Examples.cwTotalWeightZIsolatedSupport_eq_ambient_of_injOn
#assert_axioms
  AlgebraicComplexity.Examples.cwTotalWeightYZIsolatedSupport_eq_ambient_of_injOn
#assert_axioms
  AlgebraicComplexity.Examples.cwTotalWeightYCompetitorIncidence_eq_zero_of_injOn
#assert_axioms
  AlgebraicComplexity.Examples.cwTotalWeightZCompetitorIncidence_eq_zero_of_injOn
#assert_axioms
  AlgebraicComplexity.Examples.cwTotalWeight_card_ambient_le_two_mul_card_YZIsolatedSupport_of_injOn
