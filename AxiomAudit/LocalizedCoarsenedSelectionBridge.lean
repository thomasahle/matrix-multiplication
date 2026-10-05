/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.LocalizedCoarsenedSelectionBridge

set_option autoImplicit false

/-! Focused trust audit for the box/select normal-form bridge of a localized fiber selection. -/

#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.box_eq_select_of_mem_iff
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.box_coarseningFiberSelectParts_eq_select
