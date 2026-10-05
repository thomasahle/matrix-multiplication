/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutCountInputs

set_option autoImplicit false

/-! # Axiom audit for the counting inputs of the seed selection

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:44-50, 130-140`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_cut_hquarter
#assert_axioms AlgebraicComplexity.Examples.dwz63_cut_frame
#assert_axioms AlgebraicComplexity.Examples.dwz63_cut_huseful
#assert_axioms AlgebraicComplexity.Examples.dwz63_cut_componentInjOn
#assert_axioms AlgebraicComplexity.Examples.dwz63_cut_hcompType
#assert_axioms AlgebraicComplexity.Examples.dwz63_cut_hTypical
#assert_axioms AlgebraicComplexity.Examples.dwz63_cut_hV
#assert_axioms AlgebraicComplexity.Examples.dwz63_cut_hcompetitors
#assert_axioms AlgebraicComplexity.Examples.dwz63_cut_hzIndex
