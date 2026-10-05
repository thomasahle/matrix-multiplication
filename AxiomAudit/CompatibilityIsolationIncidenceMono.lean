/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.CompatibilityIsolationIncidenceMono

set_option autoImplicit false

/-! # Axiom audit for monotonicity of the compatibility competitor incidence -/

#assert_axioms AlgebraicComplexity.Tensor.compatibilityCompetitors_mono
#assert_axioms AlgebraicComplexity.Tensor.compatibilityCompetitorIncidence_mono
#assert_axioms
  AlgebraicComplexity.Tensor.card_le_card_YZCompatibilityIsolatedSupport_add_ambientBudgets
