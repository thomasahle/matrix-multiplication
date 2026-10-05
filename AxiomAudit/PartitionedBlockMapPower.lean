/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PartitionedBlockMapPower

/-! # Axiom audit for blockwise maps through positive partitioned powers

The two readings of a successor power, the split-injectivity of a block inclusion and the
unembedded form of the constituent identity it yields, the word-level blockwise map, the three
lifted hypotheses, and the packaged restriction of every positive power. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Tensor.mem_positivePower_succ_support
#assert_axioms AlgebraicComplexity.Tensor.positivePower_succ_constituent
#assert_axioms AlgebraicComplexity.Tensor.map_blockInclude_injective
#assert_axioms AlgebraicComplexity.Tensor.map_partitionedBlockMap_constituent
#assert_axioms AlgebraicComplexity.Tensor.positiveWordBlockMap
#assert_axioms AlgebraicComplexity.Tensor.map_positiveWordBlockMap_constituent
#assert_axioms AlgebraicComplexity.Tensor.positivePower_support_image
#assert_axioms AlgebraicComplexity.Tensor.positiveWordMap_injOn_support
#assert_axioms AlgebraicComplexity.Tensor.Restricts.partitionedBlockMap_positivePower
