/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedProductCore
import AxiomAudit.Command

/-! Axiom audit for finite partitioned external products. -/

open AlgebraicComplexity.Tensor

#assert_axioms blockAddressProductEquiv
#assert_axioms blockAddressProductEquiv_apply_fst
#assert_axioms blockAddressProductEquiv_apply_snd
#assert_axioms PartitionedTensor.external
#assert_axioms PartitionedTensor.mem_external_support
#assert_axioms PartitionedTensor.card_external_support
