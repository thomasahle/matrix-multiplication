/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedProductReindex
import AxiomAudit.Command

/-! Axiom audit for reindexing partitioned external products. -/

open AlgebraicComplexity.Tensor

#assert_axioms productBlockCommEquiv
#assert_axioms productBlockSpaceCommEquiv
#assert_axioms productBlockSwapRightEquiv
#assert_axioms productBlockSpaceSwapRightEquiv
#assert_axioms PartitionedTensor.external_reindex_comm
#assert_axioms PartitionedTensor.external_reindex
#assert_axioms PartitionedTensor.external_reindex_swap_right
