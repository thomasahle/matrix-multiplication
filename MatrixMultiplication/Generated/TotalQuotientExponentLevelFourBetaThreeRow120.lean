import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeDataShape20
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

/-!
# Bounded positive beta-three row 120

Each coordinate is checked through a literal midpoint after output regions `0,1,2`.  Keeping all
six bounded three-region reductions in one row module amortizes their common import closure while
staying below the kernel-memory threshold that a single six-region reduction can exceed.
Certificate: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row120

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Exact accumulator after output regions `0,1,2`. -/
def row120Coordinate0Middle : Array ℕ := #[50465748287488, 0, 0, 174628790075392, 0, 50401843871744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row120Coordinate0_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 0 =
        row120Coordinate0Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row120Coordinate0Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row120Coordinate0_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 0
        row120Coordinate0Middle =
          BetaThree.row120Coordinate0 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row120Coordinate0Middle
    BetaThree.row120Coordinate0
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row120Coordinate0_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 0 =
        BetaThree.row120Coordinate0 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 0
      row120Coordinate0Middle
      BetaThree.row120Coordinate0
      row120Coordinate0_firstHalf_eq
      row120Coordinate0_secondHalf_eq

/-- Exact accumulator after output regions `0,1,2`. -/
def row120Coordinate1Middle : Array ℕ := #[3658238394368, 0, 134026148970496, 0, 0, 134089885614080, 0, 0, 0, 0, 0, 0, 3722109255680, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row120Coordinate1_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 1 =
        row120Coordinate1Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row120Coordinate1Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row120Coordinate1_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 1
        row120Coordinate1Middle =
          BetaThree.row120Coordinate1 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row120Coordinate1Middle
    BetaThree.row120Coordinate1
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row120Coordinate1_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 1 =
        BetaThree.row120Coordinate1 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 1
      row120Coordinate1Middle
      BetaThree.row120Coordinate1
      row120Coordinate1_firstHalf_eq
      row120Coordinate1_secondHalf_eq

/-- Exact accumulator after output regions `0,1,2`. -/
def row120Coordinate2Middle : Array ℕ := #[3836395651072, 0, 133911761911808, 0, 0, 133975632773120, 0, 0, 0, 0, 0, 0, 3772591898624, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row120Coordinate2_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 2 =
        row120Coordinate2Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row120Coordinate2Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row120Coordinate2_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 2
        row120Coordinate2Middle =
          BetaThree.row120Coordinate2 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row120Coordinate2Middle
    BetaThree.row120Coordinate2
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row120Coordinate2_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 2 =
        BetaThree.row120Coordinate2 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 2
      row120Coordinate2Middle
      BetaThree.row120Coordinate2
      row120Coordinate2_firstHalf_eq
      row120Coordinate2_secondHalf_eq


/-- Assemble this global beta-three row from its three bounded coordinate checks. -/
theorem row120_eq :
    betaThreeGlobalRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 120 = BetaThree.row120 := by
  unfold BetaThree.row120
  apply betaThreeGlobalRowFor_eq_of_positive
  · decide
  · exact row120Coordinate0_eq
  · exact row120Coordinate1_eq
  · exact row120Coordinate2_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row120
