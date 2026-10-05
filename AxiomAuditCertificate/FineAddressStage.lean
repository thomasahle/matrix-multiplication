/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.FineAddressStage

/-!
# Certificate axiom audit for the single-constituent fine-address stage

`MatrixMultiplication/FineAddressStage.lean` imports the total-weight sequence packaging and
therefore reaches the generated `e7987` scalar data through it, so — exactly as for
`AxiomAuditCertificate/SimplifiedSequencePackaging.lean` — its assertions belong to the opt-in
certificate audit target rather than the ordinary focused one.  This module is also what makes the
two new sources reachable from a configured build target without editing a foreign umbrella.

Covered here, in dependency order:

* the candidate-independent layer-3 additions of
  `AlgebraicComplexity/MatrixMultiplication/SingleConstituentStage.lean`: the positive-power and
  summed-power laws for rectangular exact restrictions, and the copy-count-`1` stage constructor;
* the letter census of E2's mass-`19` fine address (`304` letters, `295` of them one-type), in CW
  leg order since the 2026-08-28 rotation (C1b item 10);
* the three exact integer comparisons `2 ^ 225 ≤ 5 ^ 97`, `2 ^ 227 ≤ 5 ^ 98`, `2 ^ 232 ≤ 5 ^ 100`
  and their per-repetition forms, plus the two negative controls that make the leg pairing a fact;
* the four committed `CW₅` letterwise block restrictions as this client reads them;
* the fine-address restriction of the stride block, its base-two shadow, the three stages built
  from them, and the two forms the sequence packaging consumes.
-/

#assert_axioms AlgebraicComplexity.Tensor.Restricts.power_matrixMultiplication
#assert_axioms AlgebraicComplexity.Tensor.Restricts.powerAdd_matrixMultiplication
#assert_axioms AlgebraicComplexity.WholeConstituentLaserVolumeStage.ofRestricts

#assert_axioms MatrixMultiplication.FineAddressStage.fineLetters_eq_strideBlockLetters
#assert_axioms MatrixMultiplication.FineAddressStage.oneTypeFineLetters_eq

#assert_axioms
  MatrixMultiplication.FineAddressStage.two_pow_xBudget_le_five_pow_xFineLetters
#assert_axioms
  MatrixMultiplication.FineAddressStage.two_pow_yBudget_le_five_pow_yFineLetters
#assert_axioms
  MatrixMultiplication.FineAddressStage.two_pow_zBudget_le_five_pow_zFineLetters
#assert_axioms
  MatrixMultiplication.FineAddressStage.leafBase_pow_xBudget_le_five_pow_xFineLetters
#assert_axioms
  MatrixMultiplication.FineAddressStage.leafBase_pow_yBudget_le_five_pow_yFineLetters
#assert_axioms
  MatrixMultiplication.FineAddressStage.leafBase_pow_zBudget_le_five_pow_zFineLetters
#assert_axioms
  MatrixMultiplication.FineAddressStage.two_pow_yBudget_not_le_five_pow_xFineLetters
#assert_axioms
  MatrixMultiplication.FineAddressStage.two_pow_zBudget_not_le_five_pow_yFineLetters
#assert_axioms MatrixMultiplication.FineAddressStage.leafExponentsValid_budget

#assert_axioms MatrixMultiplication.FineAddressStage.cwFive_restricts_xLetter
#assert_axioms MatrixMultiplication.FineAddressStage.cwFive_restricts_yLetter
#assert_axioms MatrixMultiplication.FineAddressStage.cwFive_restricts_zLetter
#assert_axioms MatrixMultiplication.FineAddressStage.cwFive_restricts_cornerLetter

#assert_axioms MatrixMultiplication.FineAddressStage.cwStrideBlock_restricts_fineAddress
#assert_axioms MatrixMultiplication.FineAddressStage.cwStrideBlock_restricts_leafBudget
#assert_axioms MatrixMultiplication.FineAddressStage.fineAddressStage
#assert_axioms MatrixMultiplication.FineAddressStage.leafBudgetStage
#assert_axioms MatrixMultiplication.FineAddressStage.belowCutoffStage
#assert_axioms
  MatrixMultiplication.FineAddressStage.polynomialDegenerates_of_count_eq_one
#assert_axioms MatrixMultiplication.FineAddressStage.retainedExtractionValid_countOne
