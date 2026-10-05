/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PartitionedSelectPositivePower

/-! # Axiom audit for block selection inside a positive partitioned power

The single declaration of the module: a positive power of a selected partitioned tensor has the
constituents of the positive power of the whole. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.positivePower_select_constituent
