/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.PooledMarginalTypeConcentration
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetCounting

/-! Focused trust audit for pooled parent-type concentration and exact recursive target counts. -/

#assert_axioms
  AlgebraicComplexity.WordType.profileConditionalEntropy_le_reference_sub_quarter_sq_of_parentDeviation
#assert_axioms
  AlgebraicComplexity.WordType.card_pooledMarginalDeviatingWords_le
#assert_axioms
  AlgebraicComplexity.Examples.mem_cwRecursiveExactTargetFiberParts_iff_conditionalTypeClass
#assert_axioms
  AlgebraicComplexity.Examples.card_cwRecursiveExactTargetFiberParts_eq_prod_multinomial
