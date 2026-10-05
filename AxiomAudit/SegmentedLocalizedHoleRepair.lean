/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedHoleRepair

set_option autoImplicit false

/-! # Axiom audit for the localized segmented Hole Lemma -/

#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.coarseningFiber_select_eq_select
#assert_axioms
  AlgebraicComplexity.Tensor.PartitionedTensor.coarseningFiber_select_eq_segmentedLocalizedSplittingPower
#assert_axioms
  AlgebraicComplexity.Tensor.PartitionedTensor.mem_segmentedLocalizedSplittingPower_support
#assert_axioms
  AlgebraicComplexity.Tensor.PartitionedTensor.segmentedLocalizedSplittingShuffle_partEquiv
#assert_axioms AlgebraicComplexity.restricts_indexedDirectSum_segmentedLocalizedHoleRepair
#assert_axioms AlgebraicComplexity.restricts_indexedDirectSum_segmentedLocalizedHoleRepair_batched
