import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow172Coordinate1Region5Child
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow172Coordinate1Region5Scaled
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeDataShape28
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

/-!
# Assembled positive beta-three coordinate 172/1, region 5

This module performs no certificate reduction.  It combines the checked unscaled child row with
the checked scale/update fold.  Certificate: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row172

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

/-- Assemble output region `5` from its bounded child and scaling checks. -/
theorem row172Coordinate1Region5_eq :
    addPositiveBetaThreeRegionFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables
      (positiveNodeAtGlobalRow 172) 1 (row172Coordinate1AfterRegion4) 5 = BetaThree.row172Coordinate1 :=
  addPositiveBetaThreeRegionFor_eq_of_child
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables
    (positiveNodeAtGlobalRow 172) 5 1
    (row172Coordinate1AfterRegion4) row172Coordinate1Region5Child BetaThree.row172Coordinate1
    row172Coordinate1Region5Child_eq
    row172Coordinate1Region5Scaled_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row172
