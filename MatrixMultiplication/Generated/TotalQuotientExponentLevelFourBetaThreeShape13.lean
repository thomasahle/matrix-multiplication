import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeDataShape13
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow78
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow79
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow80
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow81
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow82
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow83
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence


/-! Exact global beta-three shape chunk 13; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Shape13

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def expectedRows : List (Array (Array ℕ)) := BetaThree.DataShape13.expectedRows

/-- Assemble the six independently checked incoming-region rows of this fixed
positive shape. -/
theorem recurrence_eq :
    reconstructedBetaThreeShapeRowsFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 13 = expectedRows := by
  unfold expectedRows
  apply reconstructedBetaThreeShapeRowsFor_eq_of_rows
  · simpa [regionCount] using Row78.row78_eq
  · simpa [regionCount] using Row79.row79_eq
  · simpa [regionCount] using Row80.row80_eq
  · simpa [regionCount] using Row81.row81_eq
  · simpa [regionCount] using Row82.row82_eq
  · simpa [regionCount] using Row83.row83_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Shape13
