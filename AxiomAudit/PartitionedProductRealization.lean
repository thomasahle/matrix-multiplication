/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedProductRealization
import AxiomAudit.Command

/-! Axiom audit for direct-sum realization of partitioned external products. -/

open AlgebraicComplexity.Tensor

#assert_axioms partitionExternalEquiv
#assert_axioms partitionExternalEquiv_comp_blockIncludes
#assert_axioms map_partitionExternalEquiv_external_blocks
#assert_axioms map_partitionExternalEquiv_external_realize
#assert_axioms Isomorphic.partitionedExternal
