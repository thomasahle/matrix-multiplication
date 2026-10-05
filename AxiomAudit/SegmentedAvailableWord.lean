/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedAvailableWord

set_option autoImplicit false

/-! # Axiom audit for segmented available blocks -/

#assert_axioms AlgebraicComplexity.seg_segmentPermToPerm
#assert_axioms AlgebraicComplexity.segmentedShuffleUniformity_of_equiv
#assert_axioms AlgebraicComplexity.exists_segmented_shuffles_avoiding
