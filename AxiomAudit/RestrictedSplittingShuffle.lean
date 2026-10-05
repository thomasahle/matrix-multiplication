/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingShuffle

/-! Focused trust audit for the shuffling group of a restricted-splitting power: the two claims
[DuanWuZhou2022] state in `hole_lemma.tex` (the second with no proof in the source), the
uniformity of the action on available blocks, and the assembled Hole Lemma. -/

#assert_axioms AlgebraicComplexity.SplitRestriction.keeps_positionEquiv
#assert_axioms AlgebraicComplexity.SplitRestriction.keeps_positionEquiv_symm
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.restrictedSplittingShuffle
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.mem_restrictedSplittingPower_support_shuffle
#assert_axioms AlgebraicComplexity.card_availableWordShuffle_fiber
#assert_axioms AlgebraicComplexity.uniformOnAvailableWords
#assert_axioms AlgebraicComplexity.Tensor.Restricts.indexedDirectSum_restrictedSplittingHoleRepair
#assert_axioms AlgebraicComplexity.tiny_shuffle_mem_restrictedSplittingPower
