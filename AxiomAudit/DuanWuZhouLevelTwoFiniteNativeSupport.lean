/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteNativeSupport
import AxiomAudit.Command

/-! Audit of the decoded DWZ coarse-Z support consumer for [duan2023faster]. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteSplitPair_zDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteSplitPair_coarseZ
