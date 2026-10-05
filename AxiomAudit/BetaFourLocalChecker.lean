/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.BetaFourLocalChecker

/-!
# Enforcing audit for the lightweight parent-local beta-four checker

These assertions cover the cache-free arithmetic kernel used by every generated parent shard.
-/

#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalSlotData.addToRowSparse_eq_addToRow
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.scatterSparse_eq_scatter
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.gatherOn_append
