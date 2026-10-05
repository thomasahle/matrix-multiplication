import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeDataShape15
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow90
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow91
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow92
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow93
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow94
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow95
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence


/-! Exact global beta-three shape chunk 15; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Shape15

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def expectedRows : List (Array (Array ℕ)) := BetaThree.DataShape15.expectedRows

/-- Assemble the six independently checked incoming-region rows of this fixed
positive shape. -/
theorem recurrence_eq :
    reconstructedBetaThreeShapeRowsFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 15 = expectedRows := by
  unfold expectedRows
  apply reconstructedBetaThreeShapeRowsFor_eq_of_rows
  · simpa [regionCount] using Row90.row90_eq
  · simpa [regionCount] using Row91.row91_eq
  · simpa [regionCount] using Row92.row92_eq
  · simpa [regionCount] using Row93.row93_eq
  · simpa [regionCount] using Row94.row94_eq
  · simpa [regionCount] using Row95.row95_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Shape15
