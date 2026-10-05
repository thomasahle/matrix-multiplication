/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLegMarginal

set_option autoImplicit false

/-! # Axiom audit for the three leg marginals of the fifteen-cell distribution -/

#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaMarginal
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaMarginal_X
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaMarginal_Y
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaMarginal_Z
#assert_axioms AlgebraicComplexity.Examples.profileMass_dwz63AlphaMarginal
#assert_axioms AlgebraicComplexity.Examples.mappedType_legRead_dwz63AlphaAddress
#assert_axioms AlgebraicComplexity.Examples.mappedType_legRead_proportionalCounts
#assert_axioms AlgebraicComplexity.Examples.mem_cwSquareSupport_of_dwz63AlphaAddress_ne_zero
