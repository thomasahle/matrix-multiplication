/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.TypedWordMapFiberComposition

set_option autoImplicit false

/-! # Axiom audit for exact typed-word fiber disintegration -/

#assert_axioms AlgebraicComplexity.WordType.typedWordMapFiberCompEquiv
#assert_axioms AlgebraicComplexity.WordType.card_typedWordMapFiber_comp_eq_sum
