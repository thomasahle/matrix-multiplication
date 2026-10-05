/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainCopyCount

set_option autoImplicit false

/-! # Axiom audit for the plain copy count and its sixth power

The generic sixth-power step and the subexponentiality it preserves; the hash step and the copy
count at the per-position exponent; the sixth power in `Finset.card` and `Fintype.card` form; and
the wiring to the symmetrized weight. -/

#assert_axioms AlgebraicComplexity.Examples.pow_six_of_copyCount
#assert_axioms AlgebraicComplexity.Examples.subexponential_pow_six
#assert_axioms AlgebraicComplexity.Examples.dwz63_hashingBranch_pow_le_card_plainJointRetained
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainCopyCount_of_estimates
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainCopyCount_pow_six_of_estimates
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainCopyCount_pow_six_fintype
#assert_axioms AlgebraicComplexity.Examples.dwz63_symSix_weight_of_plainCopyCount
