/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.AggregateHoleFraction

set_option autoImplicit false

/-! # Axiom audit for aggregate hole fractions and the Markov retention pass -/

#assert_axioms AlgebraicComplexity.AggregateHoleFraction
#assert_axioms AlgebraicComplexity.goodCopies
#assert_axioms AlgebraicComplexity.mem_goodCopies
#assert_axioms AlgebraicComplexity.card_le_two_mul_card_goodCopies
#assert_axioms AlgebraicComplexity.card_le_two_mul_card_goodCopies_of_aggregateHoleFraction
