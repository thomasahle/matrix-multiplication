import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeDataShape20
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow120
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow121
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow122
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow123
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow124
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow125
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence


/-! Exact global beta-three shape chunk 20; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Shape20

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def expectedRows : List (Array (Array ℕ)) := BetaThree.DataShape20.expectedRows

/-- Assemble the six independently checked incoming-region rows of this fixed
positive shape. -/
theorem recurrence_eq :
    reconstructedBetaThreeShapeRowsFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 20 = expectedRows := by
  unfold expectedRows
  apply reconstructedBetaThreeShapeRowsFor_eq_of_rows
  · simpa [regionCount] using Row120.row120_eq
  · simpa [regionCount] using Row121.row121_eq
  · simpa [regionCount] using Row122.row122_eq
  · simpa [regionCount] using Row123.row123_eq
  · simpa [regionCount] using Row124.row124_eq
  · simpa [regionCount] using Row125.row125_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Shape20
