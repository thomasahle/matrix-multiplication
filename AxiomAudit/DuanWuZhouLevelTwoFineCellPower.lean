/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellPower

/-! # Axiom audit for the cell-word coherent certificates

The block-address exponent of a whole cell word, the leg-generic dimension law putting it in the
`q ^ ones` form `ZeroCoordinateMerge.mergedDimension` consumes, and the two rotated cell-word
certificates obtained by the second pass of the committed coherent recursion. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63CellOnes
#assert_axioms AlgebraicComplexity.Examples.positiveWordProduct_dwz63FineDimension_eq_pow_dwz63CellOnes
#assert_axioms AlgebraicComplexity.Examples.dwz63CellWordZeroXCoherent
#assert_axioms AlgebraicComplexity.Examples.dwz63CellWordZeroYCoherent
