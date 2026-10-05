/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellHypotheses

/-! # Axiom audit for the two fusion hypotheses of one fine cell

The profile reading of the one-slice exponent at the first live leg, and the two hypotheses of
`dwz63_fineCellPower_restricts_matrixMultiplication` discharged against the support
characterisation of the one-segment localized splitting power. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_cellOnes_eq_multiplicity_sum
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellPower_zeroLeg_eq_const
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellPower_cellOnes_eq_alphaSum_of_firstLive
