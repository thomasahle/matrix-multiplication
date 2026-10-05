/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleIntegrationAvailability

set_option autoImplicit false

/-! # Axiom audit for the availability facts of the hole-side integration

`[duan2023faster]`, section 6.3. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTilde_zDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63_joinedAlphaTilde_zDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63_coarseZ_of_segmentedAvailable
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_segmentedAvailableWord_pos
