/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleIntegrationSeedArith

set_option autoImplicit false

/-! # Axiom audit for the arithmetic steps of the seed join

`[duan2023faster]`, sections 6.2 and 6.3. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63AggregateHoleFraction_image_of_injOn
#assert_axioms AlgebraicComplexity.Examples.dwz63JointSeedCount
#assert_axioms AlgebraicComplexity.Examples.dwz63_jointSeedCount_hcount
#assert_axioms AlgebraicComplexity.Examples.dwz63_three_mul_le_sixteen_mul_jointSeedCount
#assert_axioms AlgebraicComplexity.Examples.dwz63_sum_seedSharedHoles_add_useless_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainCopyCount_pow_six_fintype_of_joint
