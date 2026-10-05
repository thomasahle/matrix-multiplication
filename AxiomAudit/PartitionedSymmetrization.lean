/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrization

set_option autoImplicit false

/-! # Axiom audit for `sym₃` and `sym₆` of a partitioned tensor -/

#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.symThreePartition
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.swapSymThreePartition
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.symSixPartition
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.card_symSixPartition_support
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.isomorphic_symThreePartition
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.isomorphic_swapSymThreePartition
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.isomorphic_symSixPartition
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.restricts_power_symSixPartition
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.restricts_power_symSix_of_partitionedStage
