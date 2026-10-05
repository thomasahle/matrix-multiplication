import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRow172Checkpoints
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

/-!
# Bounded child scatter 172/2/5, remaining slots 5,…,9

This module checks exactly five of the ten split slots in one unscaled regional child row.  The
sibling slot block and final scaling update live in separate modules.  Certificate:
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row172

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Bounded reconstruction through remaining slots 5,…,9. -/
opaque row172Coordinate2Region5ChildRemainingSlots_eq :
    betaThreeRegionRowByScatterRemainingSlotsFor
      MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables
      (positiveNodeAtGlobalRow 172) 5 2 row172Coordinate2Region5ChildFirstSlots = row172Coordinate2Region5Child := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row172Coordinate2Region5ChildFirstSlots
    row172Coordinate2Region5Child
  rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row172
