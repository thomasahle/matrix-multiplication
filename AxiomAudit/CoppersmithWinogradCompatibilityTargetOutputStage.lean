/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetOutputStage

/-! Enforcing audit for fixed-type repaired CW output stages. -/

#assert_axioms
  AlgebraicComplexity.Examples.nonempty_cwGroupedCleanup_fixedTypeTargetOutputWholeStage
