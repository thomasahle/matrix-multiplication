import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow172Coordinate0Region3Child
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow172Coordinate0Region3Scaled
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

/-!
# Assembled positive beta-three coordinate 172/0, region 3

This module performs no certificate reduction.  It combines the checked unscaled child row with
the checked scale/update fold.  Certificate: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row172

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

/-- Assemble output region `3` from its bounded child and scaling checks. -/
theorem row172Coordinate0Region3_eq :
    addPositiveBetaThreeRegionFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables
      (positiveNodeAtGlobalRow 172) 0 (row172Coordinate0AfterRegion2) 3 = row172Coordinate0AfterRegion3 :=
  addPositiveBetaThreeRegionFor_eq_of_child
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables
    (positiveNodeAtGlobalRow 172) 3 0
    (row172Coordinate0AfterRegion2) row172Coordinate0Region3Child row172Coordinate0AfterRegion3
    row172Coordinate0Region3Child_eq
    row172Coordinate0Region3Scaled_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row172
