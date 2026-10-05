/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCompatibleCut

set_option autoImplicit false

/-! # Axiom audit for `lemma:triple_implies_compatible` over the Step-1 cut

`[duan2023faster]`, section 6.1 `sec:global-algo`, claim `lemma:triple_implies_compatible`,
`papers/sources/2210.10173/global_value.tex:32-72`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_stepOneCut_isCompatible
