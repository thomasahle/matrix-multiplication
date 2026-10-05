/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.ComplementaryProductProjectionProfile

/-! Focused trust audit for the arbitrary-cell integral pooled-profile adapter. -/

#assert_axioms
  AlgebraicComplexity.ComplementaryProductProjectionModel.pooledMappedType_parentPairWord_eq_labelledCellWord
#assert_axioms
  AlgebraicComplexity.ComplementaryProductProjectionModel.isPooledMarginalProfile_of_normalized_marginals
