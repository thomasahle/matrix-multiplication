/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOmegaBound

/-! Focused trust audit for the section 6.3 bound: the explicit period family and its
factorisation, the four side conditions the endpoint asks for, the endpoint instantiated at that
family, and the closed bound `omega < 2.374631` itself.  Every declaration of the module is
asserted.

Paper step: `[duan2023faster]` section 6.3, the level-two example
(`papers/sources/2210.10173/global_value.tex:332-378`), whose stated bound is at
`global_value.tex:352`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63PeriodScale
#assert_axioms AlgebraicComplexity.Examples.dwz63PeriodScale_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63PeriodSeq
#assert_axioms AlgebraicComplexity.Examples.dwz63PeriodLen
#assert_axioms AlgebraicComplexity.Examples.dwz63_periodSeq_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_periodLen_succ
#assert_axioms AlgebraicComplexity.Examples.dwz63_le_periodSeq
#assert_axioms AlgebraicComplexity.Examples.dwz63_periodSeq_cofinal
#assert_axioms AlgebraicComplexity.Examples.dwz63_periodSeq_dvd
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_seededPeriod_applied
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631
