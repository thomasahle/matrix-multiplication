/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellUniform

/-! # Axiom audit for `huniform` away from degree two

The closed form of a fine letter's middle count, the fact that it is a function of the coarse
degree except at degree two, and the resulting letterwise-constant form of `dwz63CellOnes` over
`m + 1` positions. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwWordMiddleCount_pair
#assert_axioms AlgebraicComplexity.Examples.cwWordMiddleCount_of_degree_ne_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellOnes_of_letterwise_const
