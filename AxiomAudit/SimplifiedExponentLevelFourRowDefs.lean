/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SimplifiedExponentLevelFourRowDefs

set_option autoImplicit false

/-! Focused trust audit for the lightweight level-four top-row definitions used in the recursive
Coppersmith--Winograd analysis [coppersmith1990matrix]. -/

#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.childBits
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.regionCount
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.topBranchChunkSize
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.TopBranchRows
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.topNumeratorFrom
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.parentShapeAt
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.pairAt
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.pairIndexAt
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.topSplitNumerator
