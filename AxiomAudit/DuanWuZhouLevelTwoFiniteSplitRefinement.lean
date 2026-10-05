/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteSplitRefinement
import AxiomAudit.Command

/-! Audit of the literal finite refinement/native-letter instance for [duan2023faster]. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteProfile_nativeMass
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteSplitPair_refinesType
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteSplitPair_isUseful_degree
