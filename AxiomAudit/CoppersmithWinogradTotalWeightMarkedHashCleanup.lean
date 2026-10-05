/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightMarkedHashCleanup
import AxiomAudit.Command

/-! # Axiom audit for marked hashing followed by total-weight cleanup -/

#assert_axioms AlgebraicComplexity.Examples.cwTotalWeightYZIsolatedSupport_cycle_markedXY_eq
#assert_axioms AlgebraicComplexity.Examples.exists_seed_many_cycle_markedXY_with_totalWeight_cleanup
#assert_axioms
  AlgebraicComplexity.Examples.exists_seed_many_cycle_markedXY_with_totalWeight_cleanup_of_modulus
