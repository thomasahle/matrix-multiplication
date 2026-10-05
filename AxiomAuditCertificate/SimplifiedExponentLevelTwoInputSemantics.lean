/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SimplifiedExponentLevelTwoInputSemantics

/-!
# Certificate axiom audit for the lightweight level-two semantic bridge

The lightweight checker deliberately duplicates a small executable fragment of the established
level-two recurrence.  These assertions ensure that the lookup, geometry, single-edge, list, and
range equivalence theorems remain kernel proofs with only the project's allowlisted foundational
axioms.
-/

#assert_axioms MatrixMultiplication.SimplifiedExponentLevelTwoInput.zipLookup_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelTwoInput.findSparseRow_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelTwoInput.dyadicNumeratorAt_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelTwoInput.scalarNumeratorAt_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelTwoInput.edgeActive_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelTwoInput.edgeHeavyCoordinate_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelTwoInput.activeEdges_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelTwoInput.edgeOccurrenceNumeratorWithMassThree_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelTwoInput.edgeMuNumerator_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelTwoInput.edgeInputWithMassThree_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelTwoInput.edgeInputsWithMassThree_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelTwoInput.edgeInputRangeWithMassThree_eq
