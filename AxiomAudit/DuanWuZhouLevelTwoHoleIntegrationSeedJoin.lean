/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleIntegrationSeedJoin

set_option autoImplicit false

/-! # Axiom audit for the hole-side/count-side seed join

`[duan2023faster]`, sections 6.2 and 6.3. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_nonempty_plainJointRetainedSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_seed_holeFraction_and_copyCount
