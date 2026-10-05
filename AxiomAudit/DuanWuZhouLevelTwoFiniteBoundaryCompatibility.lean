/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteBoundaryCompatibility
import AxiomAudit.Command

/-! Audit of the finite-decoded DWZ Step-1 compatibility instance in [duan2023faster]. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteSplitPair_stepOneCut_isCompatible
