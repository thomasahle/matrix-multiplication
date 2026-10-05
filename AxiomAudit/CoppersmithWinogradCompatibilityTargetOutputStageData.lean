/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetOutputStageData

/-! Enforcing audit for sealing compatibility-cleanup data into a fixed-type output stage. -/

#assert_axioms
  AlgebraicComplexity.Examples.CWCompatibilityCleanupData.nonempty_fixedTypeTargetOutputWholeStage
