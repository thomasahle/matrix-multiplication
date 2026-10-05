/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedDivisionSymSix

/-! # Axiom audit for the iterated regional division under `sym₆`

The regional `sym₆`-weight hypothesis and the weight law it composes, which is the shape the
section 6.3 endpoint's `hleafWeight` binder consumes.

Primary source: `[duan2023faster]`, section 6.3 (the level-two global-value example),
`papers/sources/2210.10173/global_value.tex:332-348`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.SegmentedRegionalSymSixWeights
#assert_axioms AlgebraicComplexity.hasTauWeight_symSix_segmentedLocalizedSplittingPower_regional
