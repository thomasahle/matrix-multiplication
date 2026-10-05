/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityOuterStage

/-!
# Axiom audit for repaired CW outer-constituent stages

The checked declaration below is the relation-preserving boundary between sparse CW hole repair
and recursive inner extraction.  It must remain a theorem-backed exact restriction; an unproved
identification of the repaired box with a matrix-multiplication tensor would defeat the purpose of
the interface.
-/

#assert_axioms
  AlgebraicComplexity.Examples.exists_cwGroupedCleanup_repairedTargetCellType_of_sparse_count
#assert_axioms
  AlgebraicComplexity.Examples.CWCompatibilityCleanupData.repairedTargetCellTypeOuterStage_of_sparse_count
