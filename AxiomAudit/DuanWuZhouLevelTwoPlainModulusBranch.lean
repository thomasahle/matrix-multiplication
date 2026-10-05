/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainModulusBranch

/-! Focused trust audit for the second modulus branch at the plain field: the cofinal
`11 · V ≤ d`, the collapse of the joint hashing degree, and the modulus condition
`dwz63_exists_seed_aggregateHoleFraction` carries.

Paper step: `[duan2023faster]` §6.2, the asymmetric-hashing modulus
`M₀ = 8 · max(N_triple/N_X, N_α · p_comp / N_Z)`
(`papers/sources/2210.10173/global_value.tex:137`, paragraph `:130-140`), whose **second**
branch `claim:hole_frac_low` (`:247-265`) consumes.  The
three theorems audited here supply that branch at the field the endpoint chain already runs at;
they are a project-specific finite/cofinal bridge to the published claim, not a restatement of
it. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_plainHashModulus_seedSelection
#assert_axioms AlgebraicComplexity.Examples.dwz63JointHashDegree_eq_plainSharpDegree
#assert_axioms
  AlgebraicComplexity.Examples.dwz63_cofinal_eleven_mul_competitorBound_le_plainSharpDegree
