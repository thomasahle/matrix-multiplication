/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellInjective

/-! # Axiom audit for the letterwise-determination lift

The relativised word lift, the fine-letter determination it specialises to, and the fine-power
injectivity that supplies the `hx` and `hy` hypotheses of the one-slice fusion. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.positiveSupportWord_injective_of_letterwise
#assert_axioms AlgebraicComplexity.Examples.dwz63_fineLetter_eq_of_zero_of_firstLiveLeg_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_finePower_injective_firstLiveLeg
