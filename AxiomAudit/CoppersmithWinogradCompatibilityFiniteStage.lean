/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityFiniteStage

/-! Focused trust audit for the end-to-end finite CW hash/cleanup/repair stage. -/

#assert_axioms AlgebraicComplexity.Examples.cwOrientedHashCompatibilityCleanupData
#assert_axioms
  AlgebraicComplexity.Examples.nonempty_cwGroupedCleanup_fixedTypeTargetOutputWholeStage
#assert_axioms
  AlgebraicComplexity.Examples.CWCompatibilityCleanupData.nonempty_fixedTypeTargetOutputWholeStage
#assert_axioms
  AlgebraicComplexity.Examples.nonempty_cwOrientedHashCleanup_fixedTypeTargetOutputWholeStage
