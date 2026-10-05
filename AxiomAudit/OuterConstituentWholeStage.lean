/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.OuterConstituentWholeStage

/-! Focused trust audit for exact outer/inner constituent flattening. -/

#assert_axioms
  AlgebraicComplexity.OuterConstituentStage.HasExactDependentInnerExtraction
#assert_axioms
  AlgebraicComplexity.OuterConstituentStage.toWholeConstituentLaserVolumeStage_of_exactInner
