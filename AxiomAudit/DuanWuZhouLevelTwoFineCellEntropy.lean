/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellEntropy

/-! # Axiom audit for the `(0,2,2)` fine-cell entropy rate

The address-level `huniform` for a split profile on the second live leg, and the eventual
`tau`-weight of the `(0,2,2)` fine cell at any base strictly below its split profile's entropy
rate. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_cellPower_cellOnes_eq_alphaSum_of_secondLive
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_zeroXFineCellWeight
