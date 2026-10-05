/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteOrientation

/-!
# Audit of DuanWuZhouLevelTwoFiniteOrientation

Assertions for the finite physical-leg step of [duan2023faster],
`component_value.tex:459-475`. No shared-map coherence or exponent is asserted.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroX011Child
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroX011Child_decodes
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroX011Child_restricts
