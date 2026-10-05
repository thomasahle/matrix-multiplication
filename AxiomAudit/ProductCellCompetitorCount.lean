/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.ProductCellCompetitorCount

/-! Focused trust audit for exact paired-cell conditional type counting. -/

#assert_axioms AlgebraicComplexity.WordType.card_productCellConditionalTypeClass_eq_prod_multinomial
#assert_axioms
  AlgebraicComplexity.WordType.card_productCellConditionalTypeClass_eq_prod_multinomial_of_law
#assert_axioms
  AlgebraicComplexity.WordType.conditionalProfileEntropyBase_eq_prod_productCellBase
#assert_axioms AlgebraicComplexity.WordType.card_proportionalProductCellConditionalTypeClass_le
#assert_axioms AlgebraicComplexity.WordType.normalizedProfileProbability_pushforward_fst_eq
#assert_axioms
  AlgebraicComplexity.WordType.log_two_conditionalProfileEntropyBase_eq_mass_mul_conditionalEntropyBits
