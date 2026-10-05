/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleFractionRefutation

set_option autoImplicit false

/-! # Axiom audit for the refutation of the posted hole-fraction residual -/

#assert_axioms AlgebraicComplexity.Examples.card_le_card_dwz63UselessZWords_add_card_dwz63CompatibleZWords
#assert_axioms AlgebraicComplexity.Examples.card_le_card_dwz63UselessZWords_add_card_dwz63HoleSet
#assert_axioms AlgebraicComplexity.Examples.card_eq_zero_of_dwz63HoleFractionInputs
#assert_axioms AlgebraicComplexity.Examples.not_dwz63HoleFractionInputs
#assert_axioms AlgebraicComplexity.Examples.eq_empty_of_dwz63HoleFractionInputs
#assert_axioms AlgebraicComplexity.Examples.dwz63HoleFractionInputs_empty_iff
#assert_axioms AlgebraicComplexity.Examples.fifteen_mul_card_le_sixteen_mul_card_dwz63HoleSet
#assert_axioms AlgebraicComplexity.Examples.card_eq_zero_of_eight_mul_card_dwz63HoleSet_le
