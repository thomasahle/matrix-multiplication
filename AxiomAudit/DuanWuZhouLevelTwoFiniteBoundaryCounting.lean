/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteBoundaryCounting

/-! # Axiom audit for native boundary-profile counting -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Boundary_card_eq_multinomial
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Boundary_restricts_multinomial
