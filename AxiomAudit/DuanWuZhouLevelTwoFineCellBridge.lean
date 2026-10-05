/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellBridge

/-! # Axiom audit for the live-leg bridge

The fine-letter form of the live-leg middle-count symmetry, the transport of `dwz63CellOnes` onto
the leg `alphatilde` constrains, and the resulting `alphatilde`-weighted closed form --- which is
`huniform` for the split-restricted cells. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_fineLetter_middleCount_liveLegs_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellOnes_eq_sum_secondLive
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellOnes_eq_alphaTilde_sum
