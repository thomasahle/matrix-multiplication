/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.MergedLeafBudget

/-!
# Certificate axiom audit for the merged leaf's budget composition

`MatrixMultiplication/MergedLeafBudget.lean` imports the total-weight sequence packaging and hence
reaches the generated `e7987` scalar data, so its assertions live in the opt-in certificate audit
target rather than the ordinary focused one — exactly as for
`AxiomAuditCertificate/SimplifiedSequencePackaging.lean` and
`AxiomAuditCertificate/FineAddressStage.lean`.

Covered here: the `Leg`-indexed form of the committed per-leg budgets and its bridge to E1's
certificate volume-coordinate order, E2's fine/merged bit census with the three negative controls
that make the fine reading's failure a theorem on every leg, the per-repetition budget lemma, the
inequality by which a merged class dimension pays a leg budget, and the composition of a merged
stage family with a retained count into `TotalWeightTrackResidual` and the `2.36999` endpoint.
-/

#assert_axioms MatrixMultiplication.MergedLeafBudget.legBudgetOfLeg_eq_legBudget
#assert_axioms MatrixMultiplication.MergedLeafBudget.legIndex_legOfCertificateCoordinateLeg
#assert_axioms
  MatrixMultiplication.MergedLeafBudget.legBudgetOfLeg_legOfCertificateCoordinateLeg
#assert_axioms MatrixMultiplication.MergedLeafBudget.legBudgetOfLeg_add

#assert_axioms MatrixMultiplication.MergedLeafBudget.xFineLeafBits_add_xMergedGainBits
#assert_axioms MatrixMultiplication.MergedLeafBudget.yFineLeafBits_add_yMergedGainBits
#assert_axioms MatrixMultiplication.MergedLeafBudget.zFineLeafBits_add_zMergedGainBits
#assert_axioms MatrixMultiplication.MergedLeafBudget.mergedGainBits_add
#assert_axioms MatrixMultiplication.MergedLeafBudget.fineLeafBits_add_mergedGainBits
#assert_axioms MatrixMultiplication.MergedLeafBudget.xExponentBudget_not_le_xFineLeafBits
#assert_axioms MatrixMultiplication.MergedLeafBudget.yExponentBudget_not_le_yFineLeafBits
#assert_axioms MatrixMultiplication.MergedLeafBudget.zExponentBudget_not_le_zFineLeafBits
#assert_axioms MatrixMultiplication.MergedLeafBudget.not_leafExponentsValid_fine
#assert_axioms MatrixMultiplication.MergedLeafBudget.leafExponentsValid_merged

#assert_axioms MatrixMultiplication.MergedLeafBudget.leafBase_pow_mul_le_pow
#assert_axioms MatrixMultiplication.MergedLeafBudget.leafBase_pow_mul_le_mergedDimensionProduct
#assert_axioms
  MatrixMultiplication.MergedLeafBudget.leafBase_pow_mul_le_mergedDimensionProduct_of_residual
#assert_axioms MatrixMultiplication.MergedLeafBudget.retainedExtractionValid_of_mergedStageFamily
#assert_axioms MatrixMultiplication.MergedLeafBudget.totalWeightTrackResidual_of_mergedStageFamily
#assert_axioms
  MatrixMultiplication.MergedLeafBudget.omega_lt_236999_of_mergedStageFamily_at_floor
