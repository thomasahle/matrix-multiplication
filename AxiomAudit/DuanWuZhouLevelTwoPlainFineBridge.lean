/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainFineBridge

set_option autoImplicit false

/-! # Axiom audit for the coarse-to-fine bridge -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_power_restricts_finePower
#assert_axioms AlgebraicComplexity.Examples.dwz63_power_restricts_fineSelect
#assert_axioms AlgebraicComplexity.Examples.dwz63_isCompatibilitySound_selfLabel
#assert_axioms AlgebraicComplexity.Examples.dwz63_restricts_groupLabelIsolated
#assert_axioms AlgebraicComplexity.Examples.dwz63_groupLabelIsolated_hasGroupUniqueLegFibers
