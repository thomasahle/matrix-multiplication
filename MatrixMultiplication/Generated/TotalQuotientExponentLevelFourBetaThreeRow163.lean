import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeDataShape27
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

/-!
# Bounded positive beta-three row 163

Each coordinate is checked through a literal midpoint after output regions `0,1,2`.  Keeping all
six bounded three-region reductions in one row module amortizes their common import closure while
staying below the kernel-memory threshold that a single six-region reduction can exceed.
Certificate: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row163

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Exact accumulator after output regions `0,1,2`. -/
def row163Coordinate0Middle : Array ℕ := #[3979891179520, 0, 136551438745600, 0, 0, 136551438745600, 0, 0, 0, 0, 0, 0, 3979891179520, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row163Coordinate0_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 0 =
        row163Coordinate0Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row163Coordinate0Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row163Coordinate0_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 0
        row163Coordinate0Middle =
          BetaThree.row163Coordinate0 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row163Coordinate0Middle
    BetaThree.row163Coordinate0
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row163Coordinate0_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 0 =
        BetaThree.row163Coordinate0 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 0
      row163Coordinate0Middle
      BetaThree.row163Coordinate0
      row163Coordinate0_firstHalf_eq
      row163Coordinate0_secondHalf_eq

/-- Exact accumulator after output regions `0,1,2`. -/
def row163Coordinate1Middle : Array ℕ := #[3499559485440, 0, 137031770439680, 0, 0, 137031770439680, 0, 0, 0, 0, 0, 0, 3499559485440, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row163Coordinate1_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 1 =
        row163Coordinate1Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row163Coordinate1Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row163Coordinate1_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 1
        row163Coordinate1Middle =
          BetaThree.row163Coordinate1 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row163Coordinate1Middle
    BetaThree.row163Coordinate1
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row163Coordinate1_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 1 =
        BetaThree.row163Coordinate1 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 1
      row163Coordinate1Middle
      BetaThree.row163Coordinate1
      row163Coordinate1_firstHalf_eq
      row163Coordinate1_secondHalf_eq

/-- Exact accumulator after output regions `0,1,2`. -/
def row163Coordinate2Middle : Array ℕ := #[51738585333760, 0, 0, 177585489182720, 0, 51738585333760, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row163Coordinate2_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 2 =
        row163Coordinate2Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row163Coordinate2Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row163Coordinate2_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 2
        row163Coordinate2Middle =
          BetaThree.row163Coordinate2 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row163Coordinate2Middle
    BetaThree.row163Coordinate2
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row163Coordinate2_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 2 =
        BetaThree.row163Coordinate2 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 2
      row163Coordinate2Middle
      BetaThree.row163Coordinate2
      row163Coordinate2_firstHalf_eq
      row163Coordinate2_secondHalf_eq


/-- Assemble this global beta-three row from its three bounded coordinate checks. -/
theorem row163_eq :
    betaThreeGlobalRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 163 = BetaThree.row163 := by
  unfold BetaThree.row163
  apply betaThreeGlobalRowFor_eq_of_positive
  · decide
  · exact row163Coordinate0_eq
  · exact row163Coordinate1_eq
  · exact row163Coordinate2_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row163
