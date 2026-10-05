/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoIsolatedSumRate

/-! # Axiom audit for the isolated-sum and plain `sym₆` stages at a shifted leaf-value base -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwzLevelTwoCountingStage_of_isolatedSumAt
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_dwz63IsolatedSumAt
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_plainSymSixStageAt
#assert_axioms AlgebraicComplexity.Examples.dwz63_globalRate_lt_copyRate_mul_expLogVal
