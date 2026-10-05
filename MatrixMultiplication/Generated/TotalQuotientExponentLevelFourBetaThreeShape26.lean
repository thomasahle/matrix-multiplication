import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeDataShape26
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow156
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow157
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow158
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow159
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow160
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow161
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence


/-! Exact global beta-three shape chunk 26; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Shape26

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def expectedRows : List (Array (Array ℕ)) := BetaThree.DataShape26.expectedRows

/-- Assemble the six independently checked incoming-region rows of this fixed
positive shape. -/
theorem recurrence_eq :
    reconstructedBetaThreeShapeRowsFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 26 = expectedRows := by
  unfold expectedRows
  apply reconstructedBetaThreeShapeRowsFor_eq_of_rows
  · simpa [regionCount] using Row156.row156_eq
  · simpa [regionCount] using Row157.row157_eq
  · simpa [regionCount] using Row158.row158_eq
  · simpa [regionCount] using Row159.row159_eq
  · simpa [regionCount] using Row160.row160_eq
  · simpa [regionCount] using Row161.row161_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Shape26
