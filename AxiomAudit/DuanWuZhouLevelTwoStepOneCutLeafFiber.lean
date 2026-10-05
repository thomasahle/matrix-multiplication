/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutLeafFiber

set_option autoImplicit false

/-! # Axiom audit for the isolated fibre of the Step-1 cut

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:52-61, 70, 84-89, 98-102`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63CutYSupport_eq
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63CutZSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63CutIsolationHoles
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63CutIsolationHoles
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63CutGrouping_fiber_support
#assert_axioms AlgebraicComplexity.Examples.dwz63CutGrouping_fiber_select_eq
