/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.CoordinateTensorSingle

/-! # Axiom audit for the reindexed pure basis tensor

The single coordinate-algebra composite used by the partitioned block identifications. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Tensor.funLeft_coordinateTensorEquiv_single_tmul_single
