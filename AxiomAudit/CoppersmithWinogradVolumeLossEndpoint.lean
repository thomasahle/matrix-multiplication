/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeLossEndpoint
import AxiomAudit.Command

/-!
# Axiom audit for the CW volume-loss endpoint
-/

open AlgebraicComplexity.Examples

#assert_axioms retained_add_omega_mul_lowerVolume_le_cwPowerBudget
#assert_axioms omega_lt_of_cwPower_volumeLossSequence
#assert_axioms omega_lt_of_cwPower_volumeLossSequence_retainedLower
