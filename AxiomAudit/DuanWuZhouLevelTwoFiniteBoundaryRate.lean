/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteBoundaryRate
import AxiomAudit.Command

/-! Axiom audit for the native full022 boundary rate client of [duan2023faster]. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Boundary_exists_weight
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Boundary_exists_cofinalWeight
