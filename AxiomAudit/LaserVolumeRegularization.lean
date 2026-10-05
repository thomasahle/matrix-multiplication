/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeEndpointValue

/-! Focused trust audit for the laser-volume regularization bridge and its endpoint regression.

The last three asserts are the payoff check: the Coppersmith--Winograd volume endpoint reached
through the value API depends on no axioms beyond the three standard classical principles, exactly
like the committed rate route audited in `AxiomAudit/CWVolumeEndpoint.lean`. -/

#assert_axioms AlgebraicComplexity.SubexponentialLaserVolumeSequence.toTauValueCertificate
#assert_axioms AlgebraicComplexity.SubexponentialLaserVolumeSequence.exists_tauValueCertificate_term_ge
#assert_axioms AlgebraicComplexity.SubexponentialLaserVolumeSequence.le_tauValue_of_bddAbove
#assert_axioms AlgebraicComplexity.SubexponentialLaserVolumeSequence.le_tauValue
#assert_axioms AlgebraicComplexity.SubexponentialLaserVolumeSequence.laserVolumeValue_le_asymptoticRank
#assert_axioms AlgebraicComplexity.SubexponentialLaserVolumeSequence.omega_lt_three_mul_of_asymptoticRank_le
#assert_axioms AlgebraicComplexity.SubexponentialLaserVolumeSequence.omega_lt_three_mul_of_borderRankLE
#assert_axioms AlgebraicComplexity.SubexponentialLaserVolumeSequence.omega_lt_of_borderRankLE_bits
#assert_axioms AlgebraicComplexity.Examples.retained_add_omega_mul_volume_le_cwPowerBudget_value
#assert_axioms AlgebraicComplexity.Examples.omega_lt_of_cwPower_volumeSequence_value
#assert_axioms AlgebraicComplexity.Examples.omega_lt_of_cwPower_borderRankBudget
