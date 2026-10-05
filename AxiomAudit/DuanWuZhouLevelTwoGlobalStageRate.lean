/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalStageRate

/-! # Axiom audit for the count-side residual at an arbitrary rate

The rate-parameterised residual and its two consumers, with the committed statements recovered as
the instances at `dwz63TrueGlobalRate`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.DwzLevelTwoCountingStageAt
#assert_axioms AlgebraicComplexity.Examples.dwzLevelTwoCountingStageAt_trueGlobalRate
#assert_axioms AlgebraicComplexity.Examples.exists_value_of_repairedStage_atRate
#assert_axioms AlgebraicComplexity.Examples.dwzLevelTwoAssembledStage_of_countingStageAt
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_countingStageAt
#assert_axioms AlgebraicComplexity.Examples.dwzLevelTwoAssembledStage_of_countingStageAt_true
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_countingStageAt_true
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_dwz63CountingStageAt
