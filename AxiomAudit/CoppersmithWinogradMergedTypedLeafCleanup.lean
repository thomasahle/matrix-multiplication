/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradMergedTypedLeafCleanup

/-! Focused trust audit for the relaxed total-weight cleanup (C1b item 9): the constituent bridge
and the end-to-end cleanup at an arbitrary per-letter degeneration, the identification of the
committed fine dimension premise as a special case of it, the merged-leaf form, the merged
whole-constituent stage, and the statement in which the merged class dimension is visible on the
designated leg. -/

open AlgebraicComplexity.Examples

#assert_axioms cwChunk_constituentDegeneration_of_dimension_eq
#assert_axioms cwTotalWeight_coarsenedConstituent_matrixMultiplication_of_shapeType_of_degeneration
#assert_axioms
  cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_degeneration
#assert_axioms
  cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_mergedLeaf
#assert_axioms cwTotalWeightMergedCleanupStage
#assert_axioms
  cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_zeroClasses
