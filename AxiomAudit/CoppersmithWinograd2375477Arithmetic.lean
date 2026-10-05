/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinograd2375477Arithmetic

/-!
# Axiom audit for the exact arithmetic of the CW `2.375477` bound

This focused audit checks the reusable power-of-two logarithm bridge, every directed logarithm
enclosure, and the final strict rational separation independently of the tensor proof.
-/

#assert_axioms AlgebraicComplexity.Analysis.le_log_of_powTwo_add_logRatioLower
#assert_axioms AlgebraicComplexity.Analysis.log_le_of_powTwo_add_logRatioUpper
#assert_axioms AlgebraicComplexity.Examples.cw2375477_log_outer0_ge
#assert_axioms AlgebraicComplexity.Examples.cw2375477_log_outer1_ge
#assert_axioms AlgebraicComplexity.Examples.cw2375477_log_outer2_ge
#assert_axioms AlgebraicComplexity.Examples.cw2375477_log_outer3_ge
#assert_axioms AlgebraicComplexity.Examples.cw2375477_log_outer4_ge
#assert_axioms AlgebraicComplexity.Examples.cw2375477_log_fiveHundredEight_sevenths_ge
#assert_axioms AlgebraicComplexity.Examples.cw2375477_log_twoHundredFiftyFour_twoHundredFortySeven_ge
#assert_axioms AlgebraicComplexity.Examples.cw2375477_log_twelve_ge
#assert_axioms AlgebraicComplexity.Examples.cw2375477_log_thirtyEight_ge
#assert_axioms AlgebraicComplexity.Examples.cw2375477_log_six_ge
#assert_axioms AlgebraicComplexity.Examples.cw2375477_scalar_log_inequality
