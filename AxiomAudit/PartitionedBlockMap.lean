/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PartitionedBlockMap

/-! # Axiom audit for blockwise maps between partitioned tensors

The ambient map determined by a block dictionary, its action on one embedded constituent, and the
resulting exact restriction between two partitioned tensors over different block alphabets. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Tensor.partitionedBlockMap
#assert_axioms AlgebraicComplexity.Tensor.partitionedBlockMap_comp_blockInclude
#assert_axioms AlgebraicComplexity.Tensor.map_partitionedBlockMap_block
#assert_axioms AlgebraicComplexity.Tensor.Restricts.partitionedBlockMap
