/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.UnlabelledComplementaryOrbit

/-! Focused trust audit for the unlabelled complementary-orbit formulas. -/

#assert_axioms AlgebraicComplexity.WordType.sum_dualInvariant_eq_sum_representatives
#assert_axioms AlgebraicComplexity.WordType.mappedType_apply_eq_sum_representatives
#assert_axioms AlgebraicComplexity.WordType.mappedType_apply_of_complementary_pair
