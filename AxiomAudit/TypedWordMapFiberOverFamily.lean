/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.TypedWordMapFiberOverFamily

set_option autoImplicit false

/-! # Axiom audit for typed word-map fibers over finite target families -/

#assert_axioms AlgebraicComplexity.WordType.typedWordMapFiberOverFamily
#assert_axioms AlgebraicComplexity.WordType.mem_typedWordMapFiberOverFamily
#assert_axioms AlgebraicComplexity.WordType.typedWordMapFiberOverFamilyEquiv
#assert_axioms AlgebraicComplexity.WordType.card_typedWordMapFiberOverFamily_eq_sum
#assert_axioms AlgebraicComplexity.WordType.card_typedWordMapFiberOverFamily_le_mul
