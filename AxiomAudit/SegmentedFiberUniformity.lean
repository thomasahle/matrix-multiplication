/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedFiberUniformity

set_option autoImplicit false

/-! # Axiom audit for segmented fiber uniformity -/

#assert_axioms AlgebraicComplexity.segmentMultiplicity_comp_perm_general
#assert_axioms AlgebraicComplexity.segmentMultiplicity_comp_perm_symm
#assert_axioms AlgebraicComplexity.SegmentedSplitRestriction.keeps_comp_perm
#assert_axioms AlgebraicComplexity.segmentedLocalizedFiber_isomorphic_position
