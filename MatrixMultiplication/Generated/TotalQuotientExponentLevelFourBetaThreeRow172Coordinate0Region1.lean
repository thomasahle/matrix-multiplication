import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow172Coordinate0Region1Child
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow172Coordinate0Region1Scaled
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

/-!
# Assembled positive beta-three coordinate 172/0, region 1

This module performs no certificate reduction.  It combines the checked unscaled child row with
the checked scale/update fold.  Certificate: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row172

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

/-- Assemble output region `1` from its bounded child and scaling checks. -/
theorem row172Coordinate0Region1_eq :
    addPositiveBetaThreeRegionFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables
      (positiveNodeAtGlobalRow 172) 0 (row172Coordinate0AfterRegion0) 1 = row172Coordinate0AfterRegion1 :=
  addPositiveBetaThreeRegionFor_eq_of_child
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables
    (positiveNodeAtGlobalRow 172) 1 0
    (row172Coordinate0AfterRegion0) row172Coordinate0Region1Child row172Coordinate0AfterRegion1
    row172Coordinate0Region1Child_eq
    row172Coordinate0Region1Scaled_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row172
