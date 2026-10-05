/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinograd238Arithmetic

/-!
# Axiom audit for the exact arithmetic of the classical CW `2.38` bound

This focused audit checks every directed logarithm enclosure and the final strict rational
separation independently of tensor extraction, the `τ`-value calculus, and Schönhage soundness.
-/

#assert_axioms AlgebraicComplexity.Examples.cw238_log_outer0_ge
#assert_axioms AlgebraicComplexity.Examples.cw238_log_outer1_ge
#assert_axioms AlgebraicComplexity.Examples.cw238_log_outer2_ge
#assert_axioms AlgebraicComplexity.Examples.cw238_log_outer3_ge
#assert_axioms AlgebraicComplexity.Examples.cw238_log_outer4_ge
#assert_axioms AlgebraicComplexity.Examples.cw238_log_seventyFour_ge
#assert_axioms AlgebraicComplexity.Examples.cw238_log_thirtySeven_thirtySix_ge
#assert_axioms AlgebraicComplexity.Examples.cw238_log_twelve_ge
#assert_axioms AlgebraicComplexity.Examples.cw238_log_thirtyEight_ge
#assert_axioms AlgebraicComplexity.Examples.cw238_log_six_ge
#assert_axioms AlgebraicComplexity.Examples.cw238_scalar_log_inequality
