/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoEntropyXUpper

set_option autoImplicit false

/-! # Axiom audit for the upper `X` entropy atoms and the strict rate inequality -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_atom_x0_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_atom_x1_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_atom_x2_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_atom_x3_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_atom_x4_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_entropyX_le_bound
#assert_axioms AlgebraicComplexity.Examples.dwz63_logCompat_le_bound
#assert_axioms AlgebraicComplexity.Examples.dwz63_entropyZ_ge_bound
#assert_axioms AlgebraicComplexity.Examples.dwz63_logCompat_add_entropyX_lt_entropyZ
