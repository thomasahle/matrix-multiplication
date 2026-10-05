/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PartitionedPowerExternalInterchange

/-!
# Focused trust audit for positive-power/external interchange

These assertions cover the cross-type reindexing of external products, the partitioned associator
and middle-four interchange, the reindex-equivalence calculus, the letterwise and transposing word
equivalences, and the two power-level interchange laws.
-/

open AlgebraicComplexity AlgebraicComplexity.Tensor

#assert_axioms PartitionedTensor.external_reindex_congr
#assert_axioms PartitionedTensor.external_reindex_assoc
#assert_axioms PartitionedTensor.external_reindex_assoc_symm
#assert_axioms PartitionedTensor.ReindexEquiv
#assert_axioms PartitionedTensor.ReindexEquiv.refl
#assert_axioms PartitionedTensor.ReindexEquiv.trans
#assert_axioms PartitionedTensor.ReindexEquiv.congr_equiv
#assert_axioms PartitionedTensor.ReindexEquiv.external
#assert_axioms PartitionedTensor.ReindexEquiv.assoc
#assert_axioms PartitionedTensor.ReindexEquiv.assocSymm
#assert_axioms PartitionedTensor.ReindexEquiv.swapRight
#assert_axioms productBlockInterchangeEquiv
#assert_axioms PartitionedTensor.ReindexEquiv.externalInterchange
#assert_axioms positiveWordProdEquiv
#assert_axioms positiveWordEquiv_positiveWordProdEquiv
#assert_axioms positiveWordCongrEquiv
#assert_axioms positiveWordEquiv_positiveWordCongrEquiv
#assert_axioms PartitionedTensor.ReindexEquiv.positivePower
#assert_axioms PartitionedTensor.reindexEquiv_positivePower_external
#assert_axioms PartitionedTensor.reindexEquiv_positivePower_cast
