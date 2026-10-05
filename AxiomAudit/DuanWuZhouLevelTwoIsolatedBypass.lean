/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoIsolatedBypass

set_option autoImplicit false

/-! # Axiom audit for the hole-repair-free level-two bypass -/

#assert_axioms AlgebraicComplexity.hasTauWeight_permute_partitionedConstituent
#assert_axioms AlgebraicComplexity.hasTauWeight_external_partitionedConstituent
#assert_axioms AlgebraicComplexity.Examples.dwzLevelTwoCountingStage_of_isolatedSum
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_dwz63IsolatedSum
#assert_axioms AlgebraicComplexity.Examples.dwz63_globalRate_le_of_count_value
#assert_axioms AlgebraicComplexity.Examples.dwzLevelTwoCountingStage_of_weightedRestriction
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_weightedRestriction
