/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedAvailableWordShuffle

set_option autoImplicit false

/-! # Axiom audit for segmented Claim 1 and the segmented shuffling action -/

#assert_axioms AlgebraicComplexity.segmentMultiplicity_comp_perm
#assert_axioms AlgebraicComplexity.segmentMultiplicity_positiveWordPositionEquiv
#assert_axioms AlgebraicComplexity.segmentedAvailableWordShuffle_val
#assert_axioms AlgebraicComplexity.segmentedShuffleUniformity_of_fiberIndependence
