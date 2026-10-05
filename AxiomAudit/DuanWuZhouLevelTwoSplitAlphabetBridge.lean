/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSplitAlphabetBridge

set_option autoImplicit false

/-! # Axiom audit for the section 6.3 pair-alphabet split record and its bridge

Project-specific assembly, not a published theorem.  `[duan2023faster]`, section 6.1
`sec:global-algo` and section 6.3 `sec:level-2-global`,
`papers/sources/2210.10173/global_value.tex:35, 145-173, 332-375`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63FineLeftDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63SplitPair
#assert_axioms AlgebraicComplexity.Examples.dwz63SplitPair_splitCount
#assert_axioms AlgebraicComplexity.Examples.dwz63SplitPair_zIndex
#assert_axioms AlgebraicComplexity.Examples.dwz63SplitPair_boundary
#assert_axioms AlgebraicComplexity.Examples.dwz63LeftBlock
#assert_axioms AlgebraicComplexity.Examples.dwz63FineLeftDegree_leftBlock
#assert_axioms AlgebraicComplexity.Examples.dwz63_finePair_leftFibre_sum
#assert_axioms AlgebraicComplexity.Examples.dwz63_splitCount_eq_alpha_mul_leftFibre
#assert_axioms AlgebraicComplexity.Examples.dwz63_splitPair_letterPushforward
#assert_axioms AlgebraicComplexity.Examples.dwz63_matchableCompatiblePair_subset
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_matchableCompatiblePair_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_hV_pair_of_hV
