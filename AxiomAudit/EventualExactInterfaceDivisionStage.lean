/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.EventualExactInterfaceDivisionStage

/-!
# Axiom audit for eventual exact interface-division stages
-/

#assert_axioms AlgebraicComplexity.ExactInterfaceTermDivisionTree.LeafStages.toBlockedPowerPacked
#assert_axioms AlgebraicComplexity.EventualExactInterfaceDivisionStageData.count_eq_packed
#assert_axioms AlgebraicComplexity.EventualExactInterfaceDivisionStageData.xSize_eq_packed
#assert_axioms AlgebraicComplexity.EventualExactInterfaceDivisionStageData.ySize_eq_packed
#assert_axioms AlgebraicComplexity.EventualExactInterfaceDivisionStageData.zSize_eq_packed
#assert_axioms AlgebraicComplexity.EventualExactInterfaceDivisionStageData.toEventualWholeConstituentLaserVolumeLossData
