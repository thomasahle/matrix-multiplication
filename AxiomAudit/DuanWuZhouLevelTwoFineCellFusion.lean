/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellFusion

/-! # Axiom audit for the one-cell fine fusion

The letterwise reading of a constant zero-leg address, the two live-leg injectivity facts the
generic fusion asks for, the coherent shared-fibre datum, and the exact restriction of one
zero-coordinate cell of the `[duan2023faster]` section 6.3 fine leaf onto
`⟨1, |fibre| * q ^ k, 1⟩`.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3).
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_finePower_letter_eq_const_of_address
#assert_axioms AlgebraicComplexity.Examples.dwz63_fineLetter_eq_of_zero_of_liveLeg_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_finePower_injOn_liveLeg
#assert_axioms AlgebraicComplexity.Examples.dwz63FineCellSharedData
#assert_axioms AlgebraicComplexity.Examples.dwz63_fineCellPower_restricts_matrixMultiplication
