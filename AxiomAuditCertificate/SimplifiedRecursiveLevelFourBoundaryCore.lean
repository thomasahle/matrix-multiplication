/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SimplifiedRecursiveLevelFourBoundaryCore

set_option autoImplicit false

/-!
# Axiom audit for level-four boundary support geometry

These assertions cover the repeated-orientation coordinate order, the exact nonpositive
beta-three recurrence interface, and every public support/complement theorem used to realize it.
They formalize the complete-split and recursive constituent conventions of [alman2025more],
`papers/sources/2404.16349/prelim.tex:249-278` and
`papers/sources/2404.16349/constituent.tex:13-47`.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

open MatrixMultiplication.SimplifiedRecursiveLevelFourBoundary

#assert_axioms repeatedXzyCoordinateOrder
#assert_axioms repeatedXzyCoordinateOrder_agrees
#assert_axioms fixedParentCoarseIndex_repeatedXzy_x
#assert_axioms fixedParentCoarseIndex_repeatedXzy_y
#assert_axioms fixedParentCoarseIndex_repeatedXzy_z
#assert_axioms fixedParentSlotCount_repeatedXzy_X
#assert_axioms fixedParentSlotCount_repeatedXzy_Y
#assert_axioms fixedParentSlotCount_repeatedXzy_Z
#assert_axioms splitWordDepthTwoCode_mem_support
#assert_axioms ternarySupportCodes_depthTwoWord_length_le
#assert_axioms splitWordDepthTwoCode_complement
#assert_axioms ternaryComplementSlot_depthTwoWord
#assert_axioms reconstructedBetaThreeRowsFor_eq_direct
#assert_axioms FollowsNonpositiveBetaThreeRecurrence
#assert_axioms zeroCoordinate_lt_three
#assert_axioms primaryZeroLawCoordinate_lt_three
#assert_axioms complementZeroLawCoordinate_lt_three
#assert_axioms zeroThreeShapeAt_shapeEightIndex
#assert_axioms betaThreeNumeratorFrom_reconstructedBetaThreeRowsFor_of_nonpositive
#assert_axioms reconstructedBetaThreeRowsFor_followsNonpositiveBetaThreeRecurrence
#assert_axioms betaThreeWordNumerator_eq_zeroRecurrence
#assert_axioms zeroBetaThreeBaseNumerator_primary
#assert_axioms zeroBetaThreeBaseNumerator_complement
#assert_axioms betaThreeWordNumerator_complement_eq_primary
