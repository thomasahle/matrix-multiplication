/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoRegionalTarget

/-! # Axiom audit for the regional coarse targets of the section 6.3 leaf

A position of segment `t` carries `t`'s coarse letter, so the head region's piece of the
relabelled coarse target is the constant address `dwz63CellTarget`.  Eleven of the twelve
zero-coordinate rows of Table 2 are checked here; row `11`, `(2,2,0)`, and the three orbit rows
are `dwz63CellTarget_eleven` and `dwz63CellTarget_orbit` in
`Examples/DuanWuZhouLevelTwoRegionalCells.lean`.

Primary source: `[duan2023faster]`, section 6.3 (the level-two global-value example),
`papers/sources/2210.10173/global_value.tex:332-348`; Table 2 is
`papers/sources/2210.10173/global_value.tex:354-378`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_eq_zeroCellTarget
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_zero
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_one
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_two
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_three
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_four
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_five
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_eight
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_nine
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_twelve
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_thirteen
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_fourteen
#assert_axioms AlgebraicComplexity.Examples.dwz63_relabelledAddress_eq_dwz63Cell
#assert_axioms AlgebraicComplexity.Examples.dwz63_regionConst_head
#assert_axioms AlgebraicComplexity.Examples.dwz63_relabelledTarget_eq_append
