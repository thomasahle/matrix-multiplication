import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow172Checkpoints
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase

/-!
# Bounded scaled regional update 172/1/3

The unscaled child row is submitted literally.  This module checks only the `A₃` scale and the
nineteen-symbol accumulator update.  Certificate: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row172

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Bounded scale/update check for output region `3`. -/
opaque row172Coordinate1Region3Scaled_eq :
    addPositiveBetaThreeRegionFromChildFor MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables
      (positiveNodeAtGlobalRow 172) 1 (row172Coordinate1AfterRegion2) row172Coordinate1Region3Child 3 =
        row172Coordinate1AfterRegion3 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks
  rw [Pos3AData0.data_eq_rawData]
  unfold row172Coordinate1AfterRegion2
    row172Coordinate1Region3Child
    row172Coordinate1AfterRegion3
  rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row172
