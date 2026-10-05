/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.BetaFourLocalPointwise

/-!
# Enforcing audit for pointwise parent-local beta-four scattering

These assertions cover the cache-free projection theorem used to replace large closed array
reductions by bounded independent position checks.
-/

#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalSlotData.betaFourRowNumeratorAt_addToRowSparse
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.betaFourRowNumeratorAt_scatterSparseArray
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.scatterSparse_eq_scatterSparseArray_toList
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.scatterOn_range_eq_scatterSparse
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.scatterOn_range_eq_scatter
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.scatterOn_append
