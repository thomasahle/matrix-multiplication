/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedHoleMass

set_option autoImplicit false

/-! # Axiom audit for the seed-summed hole mass -/

#assert_axioms AlgebraicComplexity.Examples.dwz63FineCompetitors
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63FineCompetitors
#assert_axioms AlgebraicComplexity.Examples.dwz63SeedSharedHoles
#assert_axioms AlgebraicComplexity.Examples.dwz63BucketWitnesses
#assert_axioms AlgebraicComplexity.Examples.dwz63SeedHoleMass
#assert_axioms AlgebraicComplexity.Examples.card_dwz63SeedSharedHoles_le
#assert_axioms AlgebraicComplexity.Examples.sum_card_dwz63BucketWitnesses_mul_cube
#assert_axioms AlgebraicComplexity.Examples.sum_dwz63SeedHoleMass_mul_cube_le
