/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointMargin

/-! # Axiom audit for the leaf-value margin of the section 6.3 endpoint

The two numeric obligations of the margin variant: the shifted value still dominates the declared
margin rate, and the rank budget still clears at it. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63LeafMargin
#assert_axioms AlgebraicComplexity.Examples.dwz63ValRateMargin
#assert_axioms AlgebraicComplexity.Examples.dwz63LeafMargin_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63ValRateMargin_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_exp_leafMargin_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_valRateMargin_le_exp_sub
#assert_axioms AlgebraicComplexity.Examples.dwz63_rankBudget_lt_marginGlobalRate_pow
#assert_axioms AlgebraicComplexity.Examples.dwz63_exp_pow_six_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_assembledValue_eq_marginDemand
