/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedCore
import AxiomAudit.Command

/-! Axiom audit for finite partitioned-tensor support data. -/

open AlgebraicComplexity.Tensor

#assert_axioms PartitionedTensor.ext
#assert_axioms PartitionedTensor.mem_select_support
