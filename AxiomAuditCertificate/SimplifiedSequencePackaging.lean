/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SimplifiedSequencePackaging

/-!
# Certificate axiom audit for the total-weight track's sequence packaging

The packaging layer reaches the generated `e7987` total-weight scalar data — through
`MatrixMultiplication/TotalWeightVolumeEndpoint.lean` and
`Generated/TotalQuotientExponentStageFloors.lean` — so its assertions live in the opt-in
certificate audit target rather than the ordinary focused one, exactly as for
`AxiomAuditCertificate/SimplifiedRetainedCompressionSeam.lean`.

Re-based on 2026-08-28 with the module itself (residual **R3**).  The eab2c7 retained-compression
seam is no longer imported, so this audit no longer covers that payload; what it covers now is the
sound total-weight track.

Rotated into CW leg order on 2026-08-28 with the module (C1b item 10).

Covered here: the stride block's arithmetic and the two depth conventions, the per-leg bit budgets
`(225, 227, 232)` — E1's certificate volume-coordinate triple `(232, 225, 227)` read per leg, with
the rotation and the invariance of its total now theorems of the module — and the degenerate leaf
inequality `2 ^ 684 ≤ 2 ^ 684` that replaced
`2 ^ 705 ≤ 5 ^ 304`, the volume growth they discharge, the packaging constructor of
`SubexponentialLaserVolumeSequence`, the exact acceptance margin at the committed stage-floor sum
`8.241973` and mean volume `6`, the endpoint bridge and the milestone composition from the bundled
residual, and the value-certificate reading supplied by the B2 regularization theorem.
-/

#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.strideValue_pos
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.strideValue_cast
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.strideBlockLetters_eq
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.strideBlock_chunkAlignment
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.wordDepth_levelTwo
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.wordDepth_levelThree
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.wordDepth_levelFour
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.occurrenceDepth_levelThree
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.occurrenceDepth_levelFour
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.occurrenceDepth_add_one
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.two_pow_wordDepth_succ
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.leafExponentBudget_eq

#assert_axioms
  MatrixMultiplication.SimplifiedSequencePackaging.legBudget_legOfCertificateCoordinate
#assert_axioms
  MatrixMultiplication.SimplifiedSequencePackaging.sum_comp_legOfCertificateCoordinate
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.sum_legBudget
#assert_axioms
  MatrixMultiplication.SimplifiedSequencePackaging.sum_certificateCoordinateBudget

#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.volumeCeiling_pos
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.volumeCeiling_eq
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.two_pow_le_leafBase_pow_budget
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.two_rpow_le_leafDimensionProduct
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.two_rpow_le_leafBase_pow_budget
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.volume_growth_of_leafExponents
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.LeafExponentsValid.budget_le
#assert_axioms
  MatrixMultiplication.SimplifiedSequencePackaging.LeafExponentsValid.volumeCeiling_le
#assert_axioms
  MatrixMultiplication.SimplifiedSequencePackaging.RetainedExtractionValid.of_stageFamily
#assert_axioms MatrixMultiplication.SimplifiedSequencePackaging.retainedFloor_eq
#assert_axioms
  MatrixMultiplication.SimplifiedSequencePackaging.subexponentialLaserVolumeSequence
#assert_axioms
  MatrixMultiplication.SimplifiedSequencePackaging.nonempty_subexponentialLaserVolumeSequence_of_residual
#assert_axioms
  MatrixMultiplication.SimplifiedSequencePackaging.rankBudgetUpper_lt_endpoint_margin
#assert_axioms
  MatrixMultiplication.SimplifiedSequencePackaging.omega_lt_236999_of_sequence_at_stageFloor
#assert_axioms
  MatrixMultiplication.SimplifiedSequencePackaging.omega_lt_236999_of_totalWeightTrackResidual
#assert_axioms
  MatrixMultiplication.SimplifiedSequencePackaging.omega_lt_236999_of_totalWeightTrackResidual_at_floor
#assert_axioms
  MatrixMultiplication.SimplifiedSequencePackaging.exists_tauValueCertificate_term_ge_of_residual
