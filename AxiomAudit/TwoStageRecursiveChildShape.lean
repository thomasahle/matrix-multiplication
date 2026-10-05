/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TwoStageRecursiveChildShape
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Trust audit for two-stage recursive child shapes

These assertions cover the recursively constrained four-leaf coordinate representation motivated
by [alman2025more] `def:split-hatI`,
`papers/sources/2404.16349/prelim.tex:225-269`, and used at the forced level-two Total-Weight
quotient in `better_bound/paper.tex:1729-1801`.
-/

open AlgebraicComplexity

#assert_axioms TwoStageRecursiveChildShape
#assert_axioms TwoStageRecursiveChildShape.instFintype
#assert_axioms TwoStageRecursiveChildShape.leftComplement
#assert_axioms TwoStageRecursiveChildShape.rightParent
#assert_axioms TwoStageRecursiveChildShape.rightParent_total
#assert_axioms TwoStageRecursiveChildShape.rightComplement
#assert_axioms TwoStageRecursiveChildShape.leafCoordinate
#assert_axioms TwoStageRecursiveChildShape.coordinate
#assert_axioms TwoStageRecursiveChildShape.coordinateAddress
#assert_axioms TwoStageRecursiveChildShape.coordinate_val
#assert_axioms TwoStageRecursiveChildShape.coordinate_sum
#assert_axioms TwoStageRecursiveChildShape.coordinate_left_pair_sum
#assert_axioms TwoStageRecursiveChildShape.coordinate_right_pair_sum
#assert_axioms TwoStageRecursiveChildShape.coordinate_total
#assert_axioms TwoStageRecursiveChildShape.coordinateAddress_injective
