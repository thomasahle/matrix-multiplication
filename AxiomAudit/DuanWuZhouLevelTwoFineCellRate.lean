/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellRate

/-! # Axiom audit for the `(0,2,2)` entropy-rate bridge

The nine-term readings of a fine-letter profile's entropy and one-slice exponent, their values on
the `(0,2,2)` split row, and the identification of `tau` times the row's rate with the published
`dwz63LogVal022` --- in logarithmic and exponentiated form. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_profileEntropyNats_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_middleCountSum_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeTwo_00
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeTwo_0m
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeTwo_0l
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeTwo_m0
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeTwo_mm
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeTwo_ml
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeTwo_l0
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeTwo_lm
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeTwo_ll
#assert_axioms AlgebraicComplexity.Examples.dwz63_middleCountTwo_0l
#assert_axioms AlgebraicComplexity.Examples.dwz63_middleCountTwo_mm
#assert_axioms AlgebraicComplexity.Examples.dwz63_middleCountTwo_l0
#assert_axioms AlgebraicComplexity.Examples.dwz63_middleCountSum_alphaTilde_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_profileEntropyNats_alphaTilde_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_tau_mul_rate_eq_alphaTilde_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_tau_mul_rate_eq_alphaTilde_nine
#assert_axioms AlgebraicComplexity.Examples.dwz63_entropyRate_rpow_tau_eq_val022_pow
