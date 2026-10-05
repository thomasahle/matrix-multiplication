/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.GroupedCompatibilityCounting

/-! Focused trust audit for grouped compatibility-incidence counting. -/

#assert_axioms
  AlgebraicComplexity.Tensor.groupCompatibilityCompetitors_nonempty_of_not_isolated
#assert_axioms
  AlgebraicComplexity.Tensor.card_le_card_groupCompatibilityIsolatedSupport_add_sum_competitors
#assert_axioms
  AlgebraicComplexity.Tensor.groupCompatibilityCompetitorIncidence_le_compatibilityCompetitorIncidence
#assert_axioms
  AlgebraicComplexity.Tensor.card_le_card_groupYZCompatibilityIsolatedSupport_add_incidences
#assert_axioms
  AlgebraicComplexity.Tensor.card_le_two_mul_card_groupYZCompatibilityIsolatedSupport
#assert_axioms
  AlgebraicComplexity.Tensor.card_groupCompatibilityCompetitors_le_card_conditionalTypeClass
