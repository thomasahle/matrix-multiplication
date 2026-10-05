/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPair112Grouping

set_option autoImplicit false

/-!
# Axiom audit for the sorted-pair CW `(112)` whole-group interface

This companion enforces the trust boundary for the constant residual grouping, its complete-fiber
identities, and the factorwise restriction of every grouped positive power to four-address CW
`(112)` partitions.
-/

#assert_axioms AlgebraicComplexity.Examples.cwSortedPair112ResidualGrouping
#assert_axioms AlgebraicComplexity.Examples.cwSortedPair112ResidualGroupedTarget
#assert_axioms AlgebraicComplexity.Examples.positiveWordMap_cwSortedPair112ResidualGrouping
#assert_axioms AlgebraicComplexity.Examples.cwSortedPair112ResidualGrouping_fiber_eq
#assert_axioms AlgebraicComplexity.Examples.cwSortedPair112ResidualPositivePower_groupingFiber_eq
#assert_axioms AlgebraicComplexity.Examples.cwSortedPair112ResidualPositivePower_restricts_wordTensor
