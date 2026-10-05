/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradChunkEventualDivisionStage

/-! # Axiom audit for eventual CW chunk-division source transport -/

#assert_axioms
  AlgebraicComplexity.Examples.cwChunkEventualDivisionStageData_toCWPower
#assert_axioms
  AlgebraicComplexity.Examples.cwDepthThreeEventualDivisionStageData_toCWPowerEight
