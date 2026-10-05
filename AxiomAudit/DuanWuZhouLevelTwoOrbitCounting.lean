/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitCounting

set_option autoImplicit false

/-! # Axiom audit for the general-letter orbit counting -/

#assert_axioms AlgebraicComplexity.Examples.dwz63Alpha_six
#assert_axioms AlgebraicComplexity.Examples.dwz63Alpha_seven
#assert_axioms AlgebraicComplexity.Examples.dwz63Alpha_ten
#assert_axioms AlgebraicComplexity.Examples.dwz63OrbitOrientedCount_eq
#assert_axioms AlgebraicComplexity.Examples.three_mul_dwz63OrbitTagCount
#assert_axioms AlgebraicComplexity.Examples.dwz63BTripleCount_add_dwz63BetaTripleCount
#assert_axioms AlgebraicComplexity.Examples.bMass_dvd_dwz63BTripleCount
#assert_axioms AlgebraicComplexity.Examples.betaMass_dvd_dwz63BetaTripleCount
#assert_axioms AlgebraicComplexity.Examples.sum_dwz63OrientedCount
