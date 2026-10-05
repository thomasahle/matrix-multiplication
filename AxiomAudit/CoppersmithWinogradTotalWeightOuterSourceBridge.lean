/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightOuterSourceBridge
import AxiomAudit.Command

/-!
# Axiom audit for the total-weight outer source bridge

Checks the passage from the honest asymptotic source `(CW_q^e)^(stride · r)` to the partitioned
tensor the merged total-weight cleanup consumes, its composable form, the two ambient premises it
discharges, the non-vacuity witness for its only input, and the level-four endpoint instance at
`q = 5`, `e = 8`, `depth = 4`, `stride = 38`.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

/-! ## The bridge -/

#assert_axioms CWTotalWeightOuterCoarseCleanup.xSupport_source_restricts
#assert_axioms CWTotalWeightOuterCoarseCleanup.source_restricts_of_cleanup
#assert_axioms CWTotalWeightOuterCoarseCleanup.xSupport_cleanupPremises

/-! ## Non-vacuity -/

#assert_axioms CWTotalWeightOuterCoarseCleanup.ownLabelCleanup

/-! ## The level-four endpoint parameters -/

#assert_axioms levelFourStride38_align
#assert_axioms cwLevelFour_xSupport_source_restricts
#assert_axioms cwLevelFour_source_restricts_of_cleanup

/-! ## The stage form -/

#assert_axioms cwLevelFour_stage_of_cleanupStage
#assert_axioms cwLevelFour_stageFamily_of_cleanupStageFamily
