/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedPowerConstituent
import AxiomAudit.Command

/-!
# Axiom audit for selected constituents of partitioned powers

These checks cover the lightweight recursive partition and its exact constituent identity.
-/

open AlgebraicComplexity.Tensor

#assert_axioms PartitionedTensor.positivePower_zero
#assert_axioms PartitionedTensor.positivePower_succ
#assert_axioms PartitionedTensor.positivePower_constituent_positiveSupportWordBlockAddress
