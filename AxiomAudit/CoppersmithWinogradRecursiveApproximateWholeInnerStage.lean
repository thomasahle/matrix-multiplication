/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateWholeInnerStage

set_option autoImplicit false

/-! Focused trust audit for the A8.2 recursive approximate whole-inner stage. -/

open AlgebraicComplexity.Examples

#assert_axioms coarseningFiberSelectParts_cwRecursiveChildCoarsening_eq_exactTargetFiberParts
#assert_axioms cwRecursiveApproximateCoarsenedAlphaMarginalTerm_constituent_wholeInnerStage
