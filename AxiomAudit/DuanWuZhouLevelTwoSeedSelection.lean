/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedSelection

set_option autoImplicit false

/-! # Axiom audit for the joint seed selection -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_le_of_sum_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_holeMass_averaging_arith
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_seed_retained_and_holeMass
#assert_axioms AlgebraicComplexity.Examples.dwz63IsolatedBucket
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63IsolatedBucket
#assert_axioms AlgebraicComplexity.Examples.sum_card_dwz63SeedSharedHoles_le_holeMass
#assert_axioms AlgebraicComplexity.Examples.dwz63AggregateHoleFraction_of_bound
#assert_axioms AlgebraicComplexity.Examples.dwz63AggregateHoleFraction_image
#assert_axioms AlgebraicComplexity.Examples.dwz63AggregateHoleFraction_of_split
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_seed_aggregateHoleFraction
