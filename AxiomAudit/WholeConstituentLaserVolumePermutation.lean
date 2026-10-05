/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolumePermutation
import AxiomAudit.Command

/-!
# Axiom audit for finite whole-stage permutation
-/

open AlgebraicComplexity

#assert_axioms WholeConstituentLaserVolumeStage.permuteCycle
#assert_axioms WholeConstituentLaserVolumeStage.permuteCycleSymm
