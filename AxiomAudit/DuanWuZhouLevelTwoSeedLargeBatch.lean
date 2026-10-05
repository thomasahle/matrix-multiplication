/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedLargeBatch

set_option autoImplicit false

/-! # Axiom audit for the seed count and the uniform degree comparison

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:130-140`, with §6.2 `:179`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_plainLegTargets_nonempty
#assert_axioms AlgebraicComplexity.Examples.dwz63_hlarge_of_hbranch
#assert_axioms AlgebraicComplexity.Examples.dwz63_cofinal_eleven_mul_competitorBound_uniform
