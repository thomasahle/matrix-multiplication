/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionVolumeLoss
import AxiomAudit.Command

/-! Axiom audit for the generic loss-aware exact-division volume fold. -/

namespace AlgebraicComplexity.ExactInterfaceTermDivisionTree

#assert_axioms foldLeafBudget
#assert_axioms foldLeafBudget_leaf
#assert_axioms foldLeafBudget_branch
#assert_axioms foldLeafLoss
#assert_axioms foldLeafLoss_leaf
#assert_axioms foldLeafLoss_branch

namespace LeafStages

#assert_axioms MeetsVolumeBudgetWithLoss
#assert_axioms meetsVolumeBudgetWithLoss_leaf
#assert_axioms meetsVolumeBudgetWithLoss_branch
#assert_axioms two_rpow_foldLeafBudget_le_foldLeafLoss_mul_toPacked
#assert_axioms two_rpow_foldLeafBudget_le_foldLeafLoss_mul_toPowerPacked

end LeafStages
end AlgebraicComplexity.ExactInterfaceTermDivisionTree
