/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedInputs

set_option autoImplicit false

/-! # Axiom audit for the three inputs of the joint seed selection -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_modulus_of_compatibleSet
#assert_axioms AlgebraicComplexity.Examples.dwz63SplitCompat
#assert_axioms AlgebraicComplexity.Examples.dwz63SplitCompat_isTypical
#assert_axioms AlgebraicComplexity.Examples.card_dwz63FineCompetitors_le_card_matchableCompatible
#assert_axioms AlgebraicComplexity.Examples.dwz63_hcompetitors
#assert_axioms AlgebraicComplexity.Examples.dwz63_hzIndex
#assert_axioms AlgebraicComplexity.Examples.isUseful_of_segmentedAvailableWord
#assert_axioms AlgebraicComplexity.Examples.dwz63UselessZWords_eq_empty
#assert_axioms AlgebraicComplexity.Examples.card_dwz63UselessZWords_eq_zero
