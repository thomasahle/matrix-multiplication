/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellResum

/-! # Axiom audit for the cell-exponent re-summation

`dwz63CellOnes` as a multiplicity-weighted total, and the consequence that words of equal
empirical type carry equal exponents --- the engine of `huniform` for the split-restricted
cells. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_cellOnes_eq_sum_multiplicity
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellOnes_eq_of_multiplicity_eq
