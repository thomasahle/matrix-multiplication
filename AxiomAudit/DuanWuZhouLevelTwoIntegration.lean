/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoIntegration

set_option autoImplicit false

/-! # Axiom audit for the level-two integration wiring -/

#assert_axioms AlgebraicComplexity.Examples.dwz63IntegrationLength_succ
#assert_axioms AlgebraicComplexity.Examples.dwz63IntegrationLength_succ_scale
#assert_axioms AlgebraicComplexity.Examples.dwz63IntegrationLength_cofinal
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_openEstimates
