/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLeafTauWeightOrbit

set_option autoImplicit false

/-! # Axiom audit for the exceptional orbit's weights on all three coarse addresses -/

#assert_axioms AlgebraicComplexity.Examples.restricts_symThree_cwSquare121
#assert_axioms AlgebraicComplexity.Examples.restricts_symThree_cwSquare211
#assert_axioms AlgebraicComplexity.Examples.exists_eventually_dwz112Orbit121HasTauWeight
#assert_axioms AlgebraicComplexity.Examples.exists_eventually_dwz112Orbit211HasTauWeight
#assert_axioms AlgebraicComplexity.Examples.exists_eventually_dwz121Orbit121HasTauWeight
#assert_axioms AlgebraicComplexity.Examples.exists_eventually_dwz121Orbit211HasTauWeight
#assert_axioms AlgebraicComplexity.Examples.exists_eventually_dwz121Orbit121HasTauWeight_exp
#assert_axioms AlgebraicComplexity.Examples.exists_eventually_dwz121Orbit211HasTauWeight_exp
