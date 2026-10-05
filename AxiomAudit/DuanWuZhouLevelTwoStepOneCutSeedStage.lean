/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutSeedStage

set_option autoImplicit false

/-! # Axiom audit for the seed-selected stage over the Step-1 cut

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:98-121, 247-268`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63CutComponent
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_seed_cutStage_marked
