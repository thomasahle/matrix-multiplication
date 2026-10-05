/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightLevelTwoSquare
import AxiomAudit.Command

/-!
# Axiom audit for the depth-one total-weight / CW-square bridge
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms cwBlockDigit_val_eq_cwBlockDegree
#assert_axioms cwChunkSplitWord_one_zero
#assert_axioms cwChunkSplitWord_one_one
#assert_axioms cwChunkCoarseDigit_one_eq_cwSquareBlockDegree
#assert_axioms cwTotalWeightChunkCoarsening_one_eq_cwSquareDegreeMap
#assert_axioms cwTotalWeightCoarseSupport_one_eq_cwSquareSupport
#assert_axioms cwTotalWeightCoarseSupportOneEquivCWSquareSupport
#assert_axioms cwTotalWeightCoarseSupportOneEquivCWSquareSupport_val
