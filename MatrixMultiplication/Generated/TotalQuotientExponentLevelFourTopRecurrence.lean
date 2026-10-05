import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase

/-! Kernel reconstruction of the dense positive top cache; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.Top

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- The dense cache is exactly the positive portion of the checked sparse top table. -/
opaque recurrence_eq :
    reconstructedTopBranchRows MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables = expectedRows := by
  unfold reconstructedTopBranchRows MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  unfold expectedRows
  decide +kernel

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.Top
