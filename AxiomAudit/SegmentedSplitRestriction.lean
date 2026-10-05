/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedSplitRestriction

set_option autoImplicit false

/-! # Axiom audit for segmented split restrictions -/

#assert_axioms AlgebraicComplexity.sum_segmentMultiplicity
#assert_axioms AlgebraicComplexity.segmentMultiplicity_one
#assert_axioms AlgebraicComplexity.SegmentedSplitRestriction.ofLeg_self
#assert_axioms AlgebraicComplexity.SegmentedSplitRestriction.keeps_iff_of_some
#assert_axioms AlgebraicComplexity.segmentedKeeps_ofLeg_one_iff
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.mem_segmentedRestrictedSplittingPower_support
#assert_axioms AlgebraicComplexity.Tensor.Restricts.partitionedPositivePower_segmentedRestrictedSplittingPower
