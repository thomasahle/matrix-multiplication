import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeDataShape40
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow240
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow241
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow242
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow243
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow244
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow245
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence


/-! Exact global beta-three shape chunk 40; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Shape40

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def expectedRows : List (Array (Array ℕ)) := BetaThree.DataShape40.expectedRows

/-- Assemble the six independently checked incoming-region rows of this fixed
positive shape. -/
theorem recurrence_eq :
    reconstructedBetaThreeShapeRowsFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 40 = expectedRows := by
  unfold expectedRows
  apply reconstructedBetaThreeShapeRowsFor_eq_of_rows
  · simpa [regionCount] using Row240.row240_eq
  · simpa [regionCount] using Row241.row241_eq
  · simpa [regionCount] using Row242.row242_eq
  · simpa [regionCount] using Row243.row243_eq
  · simpa [regionCount] using Row244.row244_eq
  · simpa [regionCount] using Row245.row245_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Shape40
