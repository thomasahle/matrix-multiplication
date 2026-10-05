/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAggregateBatching

set_option autoImplicit false

/-! # Axiom audit for the aggregate batching -/

#assert_axioms AlgebraicComplexity.Examples.dwz63GoodBatchSize_pos
#assert_axioms AlgebraicComplexity.Examples.card_segmentedAvailableWord_le_two_pow
#assert_axioms AlgebraicComplexity.Examples.dwz63_eight_mul_availLog_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_aggregate_hbatch
#assert_axioms AlgebraicComplexity.Examples.dwz63_aggregate_hbudget
#assert_axioms AlgebraicComplexity.Examples.dwz63GoodBatchCount_fit
#assert_axioms AlgebraicComplexity.Examples.dwz63GoodBatchCount_pos
#assert_axioms AlgebraicComplexity.Examples.card_le_four_mul_batchSize_mul_batchCount
