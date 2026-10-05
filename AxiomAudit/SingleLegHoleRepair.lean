/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.SingleLegHoleRepair

/-! Focused trust audit for the single-leg hole repair of [DuanWuZhou2022] §5: the identification
step, the Hole Lemma with and without shuffling, and the tiny inhabited regression client. -/

#assert_axioms AlgebraicComplexity.Tensor.legKeep_iff
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.sum_realize_legSelect
#assert_axioms AlgebraicComplexity.Tensor.Restricts.indexedDirectSum_legHoleRepair
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.StructureRelabeling.mem_support_blockAddressCongr
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.StructureRelabeling.holeSelect_reindex_eq
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.StructureRelabeling.holeSelect_isomorphic
#assert_axioms AlgebraicComplexity.Tensor.Restricts.indexedDirectSum_shuffledLegHoleRepair
#assert_axioms AlgebraicComplexity.Tensor.positiveWordPositionEquiv_symm
#assert_axioms AlgebraicComplexity.Tensor.tiny_indexedDirectSum_legHoleRepair
