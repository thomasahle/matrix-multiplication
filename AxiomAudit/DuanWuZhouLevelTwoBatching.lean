/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoBatching

set_option autoImplicit false

/-! # Axiom audit for the section 6.3 batching -/

#assert_axioms AlgebraicComplexity.Examples.mul_prod_lt_pow_of_eight_mul_le
#assert_axioms AlgebraicComplexity.Examples.blockIndex_lt
#assert_axioms AlgebraicComplexity.Examples.blockBatch_apply
#assert_axioms AlgebraicComplexity.Examples.blockBatch_surjective
#assert_axioms AlgebraicComplexity.Examples.card_le_blockBatch_fiber
#assert_axioms AlgebraicComplexity.Examples.card_le_two_mul_card_blockBatch
#assert_axioms AlgebraicComplexity.Examples.card_positiveWord
#assert_axioms AlgebraicComplexity.Examples.card_pairAlphabet
#assert_axioms AlgebraicComplexity.Examples.card_segmentedAvailableWord_le
#assert_axioms AlgebraicComplexity.Examples.card_segmentedAvailableWord_lt_eight_pow
#assert_axioms AlgebraicComplexity.Examples.dwz63Batch_surjective
#assert_axioms AlgebraicComplexity.Examples.dwz63_hbudget
#assert_axioms AlgebraicComplexity.Examples.card_le_two_mul_batchSize_mul_card_batches
#assert_axioms AlgebraicComplexity.Examples.dwz63Batch_index_pos
