/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellSupport

/-! # Axiom audit for the zero-coordinate determination lemmas

A supported zero-coordinate Coppersmith--Winograd letter is pinned by its label on either live
leg, and the word-level lift of the first-live-leg form.  These are the letterwise and word-level
content of the `hx` and `hy` injectivity hypotheses of the one-slice fusion. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwSupported_eq_of_zero_of_firstLiveLeg_eq
#assert_axioms AlgebraicComplexity.Examples.cwSupported_eq_of_zero_of_secondLiveLeg_eq
#assert_axioms AlgebraicComplexity.Examples.positiveSupportWord_injective_of_zero_firstLiveLeg
