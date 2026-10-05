/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutStage

set_option autoImplicit false

/-! # Axiom audit for the section 6.3 stage over the Step-1 cut

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:52-61, 72, 84-89, 98-104`, with
`hole_lemma.tex:159-168`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_cutStage_of_claim3
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainCutStage_of_claim3
