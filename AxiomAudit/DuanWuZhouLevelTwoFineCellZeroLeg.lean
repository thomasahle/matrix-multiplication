/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellZeroLeg

/-! # Axiom audit for the constant shared leg of a zero-coordinate cell

The degree-zero fine letter is the constant zero pair, the generic constant-image word lift, and
their composite in the shape the one-slice fusion's `hz` hypothesis consumes. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwSquareBlockDegree_eq_zero_iff
#assert_axioms AlgebraicComplexity.Examples.positiveWordConst_of_positiveWordMap_const
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroLegWord_eq_const
