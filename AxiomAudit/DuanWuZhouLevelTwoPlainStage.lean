/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainStage

set_option autoImplicit false

/-! # Axiom audit for the plain-power stage onto a uniform leaf

The plain stage in the shape `restricts_power_symSix_of_plainStage` consumes, and the `sym₆` stage
it yields, in which the sixth power of the copy count comes out for free. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_plainStage_of_uniformLeaf
#assert_axioms AlgebraicComplexity.Examples.dwz63_restricts_power_symSix_of_plainStage
