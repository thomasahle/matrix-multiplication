/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.CoarsenedConstituentWholeStage

set_option autoImplicit false

/-! Focused trust audit for packaging one coarse constituent as a whole-constituent stage. -/

#assert_axioms AlgebraicComplexity.Tensor.Restricts.coarsen_constituent_wholeInnerStage
