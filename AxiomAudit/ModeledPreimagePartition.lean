/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.ModeledPreimagePartition

set_option autoImplicit false

/-! # Axiom audit for the modeled preimage partition and its exact support equality -/

#assert_axioms AlgebraicComplexity.Tensor.modeledPreimageSupport
#assert_axioms AlgebraicComplexity.Tensor.mem_modeledPreimageSupport
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.modeledPreimagePartition
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.modeledPreimagePartition_support
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.modeledPreimagePartition_constituent
#assert_axioms
  AlgebraicComplexity.Tensor.PartitionedTensor.modeledPreimagePartition_support_eq_image
#assert_axioms AlgebraicComplexity.Tensor.mem_modeledPreimageSupport_external
#assert_axioms
  AlgebraicComplexity.Tensor.PartitionedTensor.external_modeledPreimagePartition_support_eq_image
#assert_axioms AlgebraicComplexity.Tensor.Restricts.regionalSource_to_coarsePreimagePartition
