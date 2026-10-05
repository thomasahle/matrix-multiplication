/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.TotalQuotientExponentLevelFourCertificate

/-!
# Enforcing audit for the compact total-weight level-four analytic certificate

This opt-in audit covers the common-denominator term checker, the compact generated theorem, both
exact recurrence identifications, and their paper-facing semantic handoff.  Building it checks the
entire generated certificate closure while keeping that cost out of ordinary tensor and
matrix-multiplication targets.
-/

#assert_axioms
  MatrixMultiplication.SignedDyadicLogCertificate.weightedLowerWithScale_le_natLogSum
#assert_axioms
  MatrixMultiplication.SignedDyadicLogCertificate.natLogSum_le_weightedUpperWithScale
#assert_axioms
  MatrixMultiplication.SignedDyadicLogCertificate.LowerBound.eval_eq_of_constant_eq_of_terms_perm
#assert_axioms MatrixMultiplication.SignedDyadicLogCertificate.LowerBound.reorder
#assert_axioms MatrixMultiplication.RationalDyadicLog.cast_numeratorLogLower
#assert_axioms MatrixMultiplication.RationalDyadicLog.cast_numeratorLogUpper
#assert_axioms MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
#assert_axioms MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
#assert_axioms
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.levelFourFloor_le_branchRate
#assert_axioms
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.Top.recurrence_eq
#assert_axioms
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.recurrence_eq
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentLevelFourCertificate.levelFourRate_eq_generated
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentLevelFourCertificate.levelFourFloor_le_levelFourRate
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentLevelFourCertificate.branchFloorCertified
#assert_axioms
  MatrixMultiplication.TotalQuotientExponentLevelFourCertificate.levelFourFamilyFloor_le_familyExponent
