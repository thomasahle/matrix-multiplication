/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutStageUnconditional

set_option autoImplicit false

/-! # Axiom audit for the unconditional six-orientation stage over the Step-1 cut

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:98-121`, with `hole_lemma.tex:111-121, 159-168`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_plainCutSymSixStage_of_claim3
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainCutSymSixStage
