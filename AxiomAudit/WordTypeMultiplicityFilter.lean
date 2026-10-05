/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.WordTypeMultiplicityFilter

set_option autoImplicit false

/-! # Axiom audit for the `multiplicity`/position-filter bridge -/

#assert_axioms AlgebraicComplexity.WordType.multiplicity_eq_card_filter
#assert_axioms AlgebraicComplexity.WordType.multiplicity_eq_card_filter_of_decidableEq
#assert_axioms AlgebraicComplexity.WordType.card_filter_eq_multiplicity
