/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightCyclicIsolation
import AxiomAudit.Command

/-! # Axiom audit for cyclic total-weight compatibility isolation -/

#assert_axioms AlgebraicComplexity.Examples.cwTotalWeightYZIsolatedSupport_cycle_permuted_eq_of_xy
#assert_axioms AlgebraicComplexity.Examples.cwTotalWeightYCompetitorIncidence_cycle_permuted_eq_zero_of_xy
#assert_axioms AlgebraicComplexity.Examples.cwTotalWeightZCompetitorIncidence_cycle_permuted_eq_zero_of_xy
