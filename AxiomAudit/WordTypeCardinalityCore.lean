/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordTypeCardinalityCore
import AxiomAudit.Command

set_option autoImplicit false

/-! Axiom audit for the lightweight exact type-class cardinality theorem. -/

#assert_axioms AlgebraicComplexity.WordType.card_typeClass_eq_multinomial_light
