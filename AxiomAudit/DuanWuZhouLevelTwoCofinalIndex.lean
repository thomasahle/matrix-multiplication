/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCofinalIndex

set_option autoImplicit false

/-! # Axiom audit for the level-two cofinal index -/

#assert_axioms AlgebraicComplexity.Examples.dwz63CofinalIndex_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63CofinalIndex_cofinal
#assert_axioms AlgebraicComplexity.Examples.six_mul_dwz63CofinalIndex
#assert_axioms AlgebraicComplexity.Examples.dwz63Alpha_mass_dvd_six_mul_cofinalIndex
#assert_axioms AlgebraicComplexity.Examples.orbitMass_dvd_six_mul_cofinalIndex
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_dwz63IsolatedSum_cofinalIndex
#assert_axioms AlgebraicComplexity.Examples.dwz63Alpha_mass_dvd_cofinalIndex
#assert_axioms AlgebraicComplexity.Examples.orbitMass_dvd_cofinalIndex
#assert_axioms AlgebraicComplexity.Examples.sum_dwz63Alpha_mul_scale
#assert_axioms AlgebraicComplexity.Examples.six_mul_position_multiplicity
#assert_axioms AlgebraicComplexity.Examples.sum_oriented_multiplicity
#assert_axioms AlgebraicComplexity.Examples.exp_dwz63LogVal_pow_six_mul_cofinalIndex
