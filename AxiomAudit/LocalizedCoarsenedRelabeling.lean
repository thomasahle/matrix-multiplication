/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.LocalizedCoarsenedRelabeling

set_option autoImplicit false

/-! # Axiom audit for the two-predicate localized relabeling -/

#assert_axioms AlgebraicComplexity.Tensor.relabelParts_coarseningFiberSelectParts_two
#assert_axioms
  AlgebraicComplexity.Tensor.Isomorphic.positivePower_localizedCoarseningFiberSelect_position_two
