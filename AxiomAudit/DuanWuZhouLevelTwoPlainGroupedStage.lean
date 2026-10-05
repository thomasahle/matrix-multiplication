/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainGroupedStage

set_option autoImplicit false

/-! # Axiom audit for the grouped retained direct sum -/

#assert_axioms AlgebraicComplexity.Examples.dwz63PlainCoarseGroup
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainCoarseGroup_eq_of_x
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainCoarseGroup_hasGroupUniqueLegFibers_x
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainCoarseGroup_hasGroupUniqueLegFibers_y
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainUsefulCompatible
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainGroupedZSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63_mem_plainGroupedZSupport_of_notMem_holes
#assert_axioms AlgebraicComplexity.Examples.dwz63_isCompatibilitySound_plainUseful
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainBrokenGroup
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainGroupedBrokenDirectSum
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainGroupedStage_of_brokenLeaf
