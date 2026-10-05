/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutDomination

set_option autoImplicit false

/-! # Axiom audit for the domination on the Step-1 cut

`[duan2023faster]`, section 6.1 `sec:global-algo`, claim `claim:hole_frac_low`,
`papers/sources/2210.10173/global_value.tex:249-265` (necessary condition at `:255`). -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_cutReferenceHoles_subset_seedSharedHoles
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_cutReferenceHoles_le_seedSharedHoles
