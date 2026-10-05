/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAlphaAddressCells

set_option autoImplicit false

/-! # Axiom audit for the `alpha` profile at the exceptional coarse addresses -/

#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaAddress_apply
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaAddress_cellAddress
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaAddress_112
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaAddress_121
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaAddress_211
