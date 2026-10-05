/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionStage
import AxiomAudit.Command

/-!
# Axiom audit for exact interface-division stage assembly
-/

open AlgebraicComplexity

#assert_axioms WholeConstituentLaserVolumeStage.Packed.precompose
#assert_axioms WholeConstituentLaserVolumeStage.Packed.external
#assert_axioms ExactInterfaceTermDivisionTree.LeafStages.toPacked
#assert_axioms ExactInterfaceTermDivisionTree.LeafStages.toPowerPacked
