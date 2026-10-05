/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteBoundaryProfile

/-! # Axiom audit for the literal full022 native boundary-profile constructor -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63Row022BoundaryData
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Boundary_decodes
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Boundary_counts
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Boundary_restricts
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Boundary_nonempty
