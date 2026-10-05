/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellZeroZ

/-! # Axiom audit for the two zero-`Z` cells

The zero-`Z` witness readings, the free two-letter injection bounding the fibre below by
`2 ^ (n+1)`, the constant one-slice exponent, the fused weight, the two point-mass rows, the exact
`12 ^ (n+1)` value identity, and the `(1,3,0)` / `(3,1,0)` cell weights in exact and `eps` form. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroFineWitness_Y_of_Z
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroFineWitness_coarsens_Z
#assert_axioms AlgebraicComplexity.Examples.dwz63_two_pow_le_zeroZFineCellSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellPower_cellOnes_of_zeroZ
#assert_axioms AlgebraicComplexity.Examples.dwz63_hasTauWeight_zeroZFineCell
#assert_axioms AlgebraicComplexity.Examples.dwz63_proportionalCounts_zeroPair
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeRow_eight
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeRow_thirteen
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroZFineCell_value_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_hasTauWeight_fineCell130
#assert_axioms AlgebraicComplexity.Examples.dwz63_hasTauWeight_fineCell310
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_eight
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_thirteen
