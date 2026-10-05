/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteBoundaryChild
import AxiomAudit.Command

/-! Axiom coverage for the native boundary child of [duan2023faster]. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63Row022BoundaryPrefix
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022BoundaryChild
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022BoundaryChild_decodes
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022BoundaryChild_profile
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022BoundaryChild_exists_cofinalWeight
