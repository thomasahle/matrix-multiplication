/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLeftPairBridge

set_option autoImplicit false

/-! # Axiom audit for the left-digit/pair bridge

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:35, 44-50, 52-61`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_finePair_of_leftDegree_of_degree
#assert_axioms AlgebraicComplexity.Examples.dwz63_profile_of_leftDegree_pushforward
#assert_axioms AlgebraicComplexity.Examples.dwz63_segmentMultiplicity_eq_iff_leftDegree
