import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeDataShape27
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

/-!
# Bounded positive beta-three row 167

Each coordinate is checked through a literal midpoint after output regions `0,1,2`.  Keeping all
six bounded three-region reductions in one row module amortizes their common import closure while
staying below the kernel-memory threshold that a single six-region reduction can exceed.
Certificate: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row167

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Exact accumulator after output regions `0,1,2`. -/
def row167Coordinate0Middle : Array ℕ := #[3641645727744, 0, 136649384132608, 0, 0, 136581016977408, 0, 0, 0, 0, 0, 0, 3709576675328, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row167Coordinate0_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 0 =
        row167Coordinate0Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row167Coordinate0Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row167Coordinate0_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 0
        row167Coordinate0Middle =
          BetaThree.row167Coordinate0 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row167Coordinate0Middle
    BetaThree.row167Coordinate0
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row167Coordinate0_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 0 =
        BetaThree.row167Coordinate0 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 0
      row167Coordinate0Middle
      BetaThree.row167Coordinate0
      row167Coordinate0_firstHalf_eq
      row167Coordinate0_secondHalf_eq

/-- Exact accumulator after output regions `0,1,2`. -/
def row167Coordinate1Middle : Array ℕ := #[4118521315328, 0, 136172072337408, 0, 0, 136172005228544, 0, 0, 0, 0, 0, 0, 4119024631808, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row167Coordinate1_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 1 =
        row167Coordinate1Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row167Coordinate1Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row167Coordinate1_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 1
        row167Coordinate1Middle =
          BetaThree.row167Coordinate1 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row167Coordinate1Middle
    BetaThree.row167Coordinate1
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row167Coordinate1_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 1 =
        BetaThree.row167Coordinate1 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 1
      row167Coordinate1Middle
      BetaThree.row167Coordinate1
      row167Coordinate1_firstHalf_eq
      row167Coordinate1_secondHalf_eq

/-- Exact accumulator after output regions `0,1,2`. -/
def row167Coordinate2Middle : Array ℕ := #[50207765037056, 0, 0, 180234527703040, 0, 50139330772992, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row167Coordinate2_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 2 =
        row167Coordinate2Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row167Coordinate2Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row167Coordinate2_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 2
        row167Coordinate2Middle =
          BetaThree.row167Coordinate2 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row167Coordinate2Middle
    BetaThree.row167Coordinate2
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row167Coordinate2_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 2 =
        BetaThree.row167Coordinate2 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 2
      row167Coordinate2Middle
      BetaThree.row167Coordinate2
      row167Coordinate2_firstHalf_eq
      row167Coordinate2_secondHalf_eq


/-- Assemble this global beta-three row from its three bounded coordinate checks. -/
theorem row167_eq :
    betaThreeGlobalRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 167 = BetaThree.row167 := by
  unfold BetaThree.row167
  apply betaThreeGlobalRowFor_eq_of_positive
  · decide
  · exact row167Coordinate0_eq
  · exact row167Coordinate1_eq
  · exact row167Coordinate2_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row167
