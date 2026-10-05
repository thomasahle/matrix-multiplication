/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHashRetention

set_option autoImplicit false

/-! # Axiom audit for level-two hash retention

The fixed hashing parameters --- ambient degree, Bertrand modulus, field, and their three
inequalities --- the ambient legal-target count and leg-fiber degree bound, the factored retention
loss, and the retention theorem itself. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63AmbientDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63AmbientDegree_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63HashModulus
#assert_axioms AlgebraicComplexity.Examples.dwz63HashModulus_char_floor
#assert_axioms AlgebraicComplexity.Examples.dwz63HashModulus_requirement
#assert_axioms AlgebraicComplexity.Examples.dwz63HashModulus_le
#assert_axioms AlgebraicComplexity.Examples.card_dwz63HashField
#assert_axioms AlgebraicComplexity.Examples.card_positiveWord_dwz63SymSix
#assert_axioms AlgebraicComplexity.Examples.card_legalTargets_univ_dwz63
#assert_axioms AlgebraicComplexity.Examples.card_legFiber_le_dwz63AmbientDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63ModulusLoss
#assert_axioms AlgebraicComplexity.Examples.dwz63BehrendLoss
#assert_axioms AlgebraicComplexity.Examples.dwz63RetentionLoss
#assert_axioms AlgebraicComplexity.Examples.dwz63RetentionLoss_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63ModulusLoss_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63BehrendLoss_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_retained_card_lower
