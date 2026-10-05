/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Probability.ComplementaryProductProjectionParentLaw

/-!
# Axiom audit for complementary-product parent laws
-/

open AlgebraicComplexity

#assert_axioms ComplementaryProductProjectionModel.parentLaw_concatSplitWords_weight
#assert_axioms ComplementaryProductProjectionModel.parentLaw_concatSplitWords_weight_eq_normalizedCounts
#assert_axioms ComplementaryOccurrenceLaw.normalizedChildLaw_weight_of_scaled_row
