/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedSplittingValue

set_option autoImplicit false

/-! # Axiom audit for the segmented localized splitting value law -/

#assert_axioms AlgebraicComplexity.mem_segmentedLocalizedSplittingPower_support_of_word
#assert_axioms AlgebraicComplexity.hasTauWeight_segmentedLocalizedSplittingPower_of_wordTensor
#assert_axioms AlgebraicComplexity.hasTauWeight_symSix_segmentedLocalizedSplittingPower_of_wordTensor
#assert_axioms AlgebraicComplexity.hasTauWeight_segmentedLocalizedSplittingPower
