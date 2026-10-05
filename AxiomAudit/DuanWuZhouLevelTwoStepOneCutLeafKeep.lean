/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutLeafKeep

set_option autoImplicit false

/-! # Axiom audit for N4: the standard-form leaf survives Additional Zeroing-Out Step 1

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:47, 52-61, 63-72, 98-102`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_stepOneKeep_of_leafAvailable
