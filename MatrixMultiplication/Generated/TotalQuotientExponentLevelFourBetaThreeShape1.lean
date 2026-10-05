import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeDataShape1
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence


/-! Exact global beta-three shape chunk 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Shape1

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def expectedRows : List (Array (Array ℕ)) := BetaThree.DataShape1.expectedRows

/-- Kernel reconstruction of all six incoming-region rows of this fixed shape. -/
opaque recurrence_eq :
    reconstructedBetaThreeShapeRowsFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 1 = expectedRows := by
  unfold reconstructedBetaThreeShapeRowsFor MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables zero3Chunks
  rw [Zero3Data0.data_eq_rawData]
  unfold expectedRows
  decide +kernel

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Shape1
