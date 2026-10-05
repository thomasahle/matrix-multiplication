/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedHoleRepair

set_option autoImplicit false

/-! # Axiom audit for the segmented Hole Lemma -/

#assert_axioms AlgebraicComplexity.segPreserving_symm
#assert_axioms AlgebraicComplexity.seg_segmentPermToPerm_symm
#assert_axioms AlgebraicComplexity.segmentMultiplicity_positionEquiv
#assert_axioms AlgebraicComplexity.SegmentedSplitRestriction.keeps_positionEquiv
#assert_axioms AlgebraicComplexity.SegmentedSplitRestriction.keeps_positionEquiv_symm
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.segmentedRestrictedSplittingShuffle_partEquiv
#assert_axioms AlgebraicComplexity.restricts_indexedDirectSum_segmentedHoleRepair
#assert_axioms AlgebraicComplexity.restricts_indexedDirectSum_segmentedHoleRepair_batched
