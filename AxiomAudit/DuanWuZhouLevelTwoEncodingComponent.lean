/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoEncodingComponent

set_option autoImplicit false

/-! # Axiom audit -/

#assert_axioms AlgebraicComplexity.Examples.dwz63ComponentWord
#assert_axioms AlgebraicComplexity.Examples.dwz63_componentWord_injOn_legalTargets
#assert_axioms AlgebraicComplexity.Examples.dwz63_zIndex_eq_encode_componentWord
#assert_axioms AlgebraicComplexity.Examples.dwz63_zIndex_eq_of_componentWord
