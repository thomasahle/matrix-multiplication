/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Probability.ComplementaryOccurrenceCellProjection

/-! Focused trust audit for arbitrary-cell normalization of complementary occurrence laws. -/

#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.mappedType_add_mappedType_comp_complement
#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.cellMass_mul_normalizedCellChildLaw_weight
#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.toCellProductProjectionModel_reference_pooledFeature_weight
