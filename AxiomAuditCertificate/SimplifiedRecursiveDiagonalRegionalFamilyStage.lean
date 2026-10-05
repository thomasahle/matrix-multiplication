/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SimplifiedRecursiveDiagonalRegionalFamilyStage

/-!
# Axiom audit for checked diagonal regional stages
-/

#assert_axioms MatrixMultiplication.SimplifiedRecursiveDiagonalRegionalFamilyStage.levelFourDiagonalSemanticRegionalStages
#assert_axioms MatrixMultiplication.SimplifiedRecursiveDiagonalRegionalFamilyStage.levelFourDiagonalSemanticDivisionTreeLeafStages
