/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightLevelTwoSemantic
import AxiomAudit.Command

/-! # Axiom audit for the depth-one total-weight / CW-square semantic adapter -/

#assert_axioms
  AlgebraicComplexity.Examples.cwTotalWeightLevelTwo_constituent_isomorphic_cwSquare
#assert_axioms
  AlgebraicComplexity.Examples.cwTotalWeightLevelTwo_constituent_restricts_cwSquare
#assert_axioms
  AlgebraicComplexity.Examples.cwSquare_constituent_restricts_cwTotalWeightLevelTwo
#assert_axioms AlgebraicComplexity.Examples.cwTotalWeightLevelTwo_realize_isomorphic_cwSquare
#assert_axioms AlgebraicComplexity.Examples.cwTotalWeightLevelTwo_realize_restricts_cwSquare
#assert_axioms AlgebraicComplexity.Examples.cwSquare_realize_restricts_cwTotalWeightLevelTwo
