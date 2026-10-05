import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeDataShape26
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

/-!
# Bounded positive beta-three row 160

Each coordinate is checked through a literal midpoint after output regions `0,1,2`.  Keeping all
six bounded three-region reductions in one row module amortizes their common import closure while
staying below the kernel-memory threshold that a single six-region reduction can exceed.
Certificate: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row160

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Exact accumulator after output regions `0,1,2`. -/
def row160Coordinate0Middle : Array ℕ := #[3737108086784, 0, 136759895654400, 0, 0, 136759862099968, 0, 0, 0, 0, 0, 0, 3737074532352, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row160Coordinate0_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 0 =
        row160Coordinate0Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row160Coordinate0Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row160Coordinate0_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 0
        row160Coordinate0Middle =
          BetaThree.row160Coordinate0 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row160Coordinate0Middle
    BetaThree.row160Coordinate0
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row160Coordinate0_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 0 =
        BetaThree.row160Coordinate0 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 0
      row160Coordinate0Middle
      BetaThree.row160Coordinate0
      row160Coordinate0_firstHalf_eq
      row160Coordinate0_secondHalf_eq

/-- Exact accumulator after output regions `0,1,2`. -/
def row160Coordinate1Middle : Array ℕ := #[51949978255360, 0, 0, 177093950308352, 0, 51950011809792, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row160Coordinate1_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 1 =
        row160Coordinate1Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row160Coordinate1Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row160Coordinate1_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 1
        row160Coordinate1Middle =
          BetaThree.row160Coordinate1 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row160Coordinate1Middle
    BetaThree.row160Coordinate1
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row160Coordinate1_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 1 =
        BetaThree.row160Coordinate1 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 1
      row160Coordinate1Middle
      BetaThree.row160Coordinate1
      row160Coordinate1_firstHalf_eq
      row160Coordinate1_secondHalf_eq

/-- Exact accumulator after output regions `0,1,2`. -/
def row160Coordinate2Middle : Array ℕ := #[3824752263168, 0, 136672184369152, 0, 0, 136672251478016, 0, 0, 0, 0, 0, 0, 3824752263168, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row160Coordinate2_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 2 =
        row160Coordinate2Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row160Coordinate2Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row160Coordinate2_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 2
        row160Coordinate2Middle =
          BetaThree.row160Coordinate2 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row160Coordinate2Middle
    BetaThree.row160Coordinate2
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row160Coordinate2_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 2 =
        BetaThree.row160Coordinate2 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 2
      row160Coordinate2Middle
      BetaThree.row160Coordinate2
      row160Coordinate2_firstHalf_eq
      row160Coordinate2_secondHalf_eq


/-- Assemble this global beta-three row from its three bounded coordinate checks. -/
theorem row160_eq :
    betaThreeGlobalRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 160 = BetaThree.row160 := by
  unfold BetaThree.row160
  apply betaThreeGlobalRowFor_eq_of_positive
  · decide
  · exact row160Coordinate0_eq
  · exact row160Coordinate1_eq
  · exact row160Coordinate2_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row160
