/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainFiberCount

set_option autoImplicit false

/-! # Axiom audit for the plain marginal-typical leg fiber -/

#assert_axioms AlgebraicComplexity.Examples.dwz63PlainLegTargets
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63PlainLegTargets
#assert_axioms AlgebraicComplexity.Examples.card_dwz63PlainLegTargets
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainMarginalWords_stable
#assert_axioms AlgebraicComplexity.Examples.card_dwz63PlainMarginalWords_eq
#assert_axioms AlgebraicComplexity.Examples.card_sourceWordLegFiber_le_sharpDegree
