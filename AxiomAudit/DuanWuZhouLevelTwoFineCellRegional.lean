/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellRegional

/-! # Axiom audit for the regional weight of a zero-coordinate fine cell

The two arithmetic steps (the one-slice exponent scales with the period; the base-two entropy in
exponential form) and the weight of a zero-coordinate cell at its published value less an
arbitrary positive deficit. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_middleCountSum_proportional
#assert_axioms AlgebraicComplexity.Examples.dwz63_two_rpow_profileEntropyBits
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_logVal
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_zero
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_one
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_three
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_four
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_five
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_nine
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_twelve
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_fourteen
