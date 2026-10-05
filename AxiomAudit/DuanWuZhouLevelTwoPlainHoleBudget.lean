/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainHoleBudget

set_option autoImplicit false

/-! # Axiom audit for the plain-partition Hole-Lemma budget -/

#assert_axioms AlgebraicComplexity.Examples.dwz63SharedZWords
#assert_axioms AlgebraicComplexity.Examples.dwz63UselessZWords
#assert_axioms AlgebraicComplexity.Examples.dwz63CompatibleZWords
#assert_axioms AlgebraicComplexity.Examples.card_dwz63HoleSet_le
#assert_axioms AlgebraicComplexity.Examples.card_dwz63SharedZWords_le_sum
#assert_axioms AlgebraicComplexity.Examples.card_dwz63SharedZWords_le_mul
#assert_axioms AlgebraicComplexity.Examples.eight_mul_card_dwz63HoleSet_le
#assert_axioms AlgebraicComplexity.Examples.Dwz63HoleFractionInputs
#assert_axioms AlgebraicComplexity.Examples.eight_mul_card_dwz63HoleSet_le_of_inputs
#assert_axioms AlgebraicComplexity.Examples.dwz63_hbudget_of_holeBound
#assert_axioms AlgebraicComplexity.Examples.dwz63_hbudget_of_holeFractionInputs
