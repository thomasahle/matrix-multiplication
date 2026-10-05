/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedPowerSupportDecodeCore
import AxiomAudit.Command

/-! Axiom audit for the lightweight positive-power support decoder. -/

open AlgebraicComplexity.Tensor

#assert_axioms PartitionedTensor.positiveSupportWordBlockAddress_mem_positivePower_support_recursive
#assert_axioms PartitionedTensor.exists_positiveSupportWord_of_mem_positivePower_support_recursive
#assert_axioms PartitionedTensor.positiveSupportWordOfAddress
#assert_axioms PartitionedTensor.positiveSupportWordBlockAddress_positiveSupportWordOfAddress
#assert_axioms positiveWordEquiv_positiveSupportWordBlockAddress_recursive
