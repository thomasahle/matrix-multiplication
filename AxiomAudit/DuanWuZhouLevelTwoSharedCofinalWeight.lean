/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSharedCofinalWeight

/-!
# Axiom audit for the paid-margin DWZ cofinal-weight instance

Audit of [duan2023faster], section 6, `eq:value_before_nth_root`, `eq:numeric_conclusion_g`,
and the section 6.3 instance (`papers/sources/2210.10173/global_value.tex:269-309,332-378`).
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_weightedSeededPeriod
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_paidMarginReferenceLeafPeriod
#assert_axioms AlgebraicComplexity.Examples.dwz63_cofinal_hasTauWeight_paidMargin
#assert_axioms AlgebraicComplexity.Examples.dwz63_omega_lt_2374631_sharedCofinal
