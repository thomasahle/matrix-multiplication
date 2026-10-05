/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellOnes

/-! # Axiom audit for the address-level one-slice exponent

The block-address middle-digit count, its identification with the committed supported-word
statistic, and the resulting `q ^ ones` dimension law in the form
`ZeroCoordinateMerge.mergedDimension` consumes. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwWordMiddleCount
#assert_axioms AlgebraicComplexity.Examples.cwSupportedWordMiddleCount_eq_cwWordMiddleCount
#assert_axioms
  AlgebraicComplexity.Examples.positiveWordProduct_cwBaseDimension_secondLiveLeg_eq_pow_cwWordMiddleCount
