/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityProportionalStage
import AxiomAudit.Command

/-! Enforcing axiom audit for proportional finite CW compatibility stages. -/

open AlgebraicComplexity.Examples

#assert_axioms
  CWCompatibilityCleanupData.nonempty_proportionalFixedTypeTargetOutputWholeStage_of_incidence
#assert_axioms
  nonempty_cwOrientedHashCleanup_proportionalFixedTypeTargetOutputWholeStage_of_incidence
