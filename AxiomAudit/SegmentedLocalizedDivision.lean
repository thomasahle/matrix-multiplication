/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedDivision

/-! # Axiom audit for the regional division of a localized segmented leaf

Increment (i) of the section 6.3 segment factorisation: both conjuncts of
`segmentedLocalizedKeep` split across a concatenation of two consecutive position regions. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Tensor.positiveWordMap_positiveWordAppend
#assert_axioms AlgebraicComplexity.segmentMultiplicity_eq_card_fiber
#assert_axioms AlgebraicComplexity.segmentMultiplicity_append
#assert_axioms AlgebraicComplexity.segmentMultiplicity_const_self
#assert_axioms AlgebraicComplexity.segmentMultiplicity_const_of_ne
#assert_axioms AlgebraicComplexity.segmentMultiplicity_cast
#assert_axioms AlgebraicComplexity.segmentationLeft
#assert_axioms AlgebraicComplexity.segmentationRight
#assert_axioms AlgebraicComplexity.append_segmentationLeft_segmentationRight
#assert_axioms AlgebraicComplexity.segmentMultiplicity_positiveWordAppend
#assert_axioms AlgebraicComplexity.SegmentedSplitRestriction.keeps_iff
#assert_axioms AlgebraicComplexity.SegmentedSplitRestriction.keeps_append
#assert_axioms AlgebraicComplexity.SegmentedSplitRestriction.keeps_const_seg_iff
#assert_axioms AlgebraicComplexity.SegmentedSplitRestriction.ofLeg_sum
#assert_axioms AlgebraicComplexity.segmentedLocalizedKeep_append
#assert_axioms AlgebraicComplexity.Tensor.Restricts.segmentedLocalizedSplittingPower_binaryDivision
