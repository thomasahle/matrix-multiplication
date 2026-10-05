/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoRegionalCells

/-! # Axiom audit for the fifteen region entries and their value

Twelve proved cells, three orbit hypotheses in image 104's shape, and the exact value the fifteen
regions deliver against the endpoint's demand. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_eleven
#assert_axioms AlgebraicComplexity.Examples.dwz63CellTarget_orbit
#assert_axioms AlgebraicComplexity.Examples.dwz63RegionValue
#assert_axioms AlgebraicComplexity.Examples.dwz63_symSix_regionEntry_orbit
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_symSix_regionEntry_cell
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_symSix_regionEntry_cells
#assert_axioms AlgebraicComplexity.Examples.dwz63RegionExponent
#assert_axioms AlgebraicComplexity.Examples.dwz63RegionValue_eq_exp
#assert_axioms AlgebraicComplexity.Examples.dwz63_sum_alphaCast
#assert_axioms AlgebraicComplexity.Examples.dwz63_sum_regionExponent
#assert_axioms AlgebraicComplexity.Examples.dwz63_leafValue_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_expLogVal_pow_eq_expMul
#assert_axioms AlgebraicComplexity.Examples.dwz63_regionProduct_lt_required
