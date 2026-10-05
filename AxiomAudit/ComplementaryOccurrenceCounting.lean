/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceCounting

/-! Focused trust audit for occurrence-correct conditional type counting. -/

#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.card_conditionalTypeClass_eq_prod_multinomial
#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.card_proportionalConditionalTypeClass_le
#assert_axioms AlgebraicComplexity.subexponential_sup_complementaryOccurrenceLoss
#assert_axioms AlgebraicComplexity.card_proportionalComplementaryOccurrenceTypeClass_le_uniform
