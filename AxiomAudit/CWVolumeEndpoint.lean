/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeEndpoint

/-! Focused trust audit for the source-generic CW volume endpoint. -/

#assert_axioms AlgebraicComplexity.Examples.log_borderRank_coppersmithWinograd_power_le
#assert_axioms AlgebraicComplexity.Examples.retained_add_omega_mul_volume_le_cwPowerBudget
#assert_axioms AlgebraicComplexity.Examples.omega_lt_of_cwPower_volumeSequence
#assert_axioms AlgebraicComplexity.Examples.omega_lt_of_cwPower_volumeSequence_lowerBounds
