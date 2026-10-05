/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ConditionalWordTypeMultinomial
import AxiomAudit.Command

/-!
# Axiom audit for exact cellwise multinomial counts

Enforces the trust contract for both finite counting declarations in
`ConditionalWordTypeMultinomial`, the exact count underlying [alman2025more], Claim 6.18.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.WordType.card_conditionalTypeClass_eq_prod_multinomial
#assert_axioms AlgebraicComplexity.WordType.card_conditionalTypeClass_eq_prod_multinomial_of_law
