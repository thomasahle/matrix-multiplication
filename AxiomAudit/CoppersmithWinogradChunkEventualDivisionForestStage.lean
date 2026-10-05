/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradChunkEventualDivisionForestStage

/-! # Axiom audit for eventual CW chunk-division *forest* source transport -/

#assert_axioms
  AlgebraicComplexity.Examples.cwChunkEventualDivisionForestStageData_toCWPower
#assert_axioms
  AlgebraicComplexity.Examples.cwDepthThreeEventualDivisionForestStageData_toCWPowerEight
