/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellJoined

/-! # Axiom audit for the eleven cell weights at one common period

Each of the eleven zero-coordinate cells of `[duan2023faster]`'s section 6.3 leaf, restated at the
joined period `2 * 10 ^ 8 * (dwz63Alpha t * s)` --- the period at which region `t` of the leaf holds
exactly `dwz63Alpha t * scale` positions.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3).
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_joinedFineCellWeight_zero
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_joinedFineCellWeight_one
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_joinedFineCellWeight_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_joinedFineCellWeight_three
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_joinedFineCellWeight_four
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_joinedFineCellWeight_five
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_joinedFineCellWeight_eight
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_joinedFineCellWeight_nine
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_joinedFineCellWeight_twelve
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_joinedFineCellWeight_thirteen
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_joinedFineCellWeight_fourteen
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroCellTarget_append
