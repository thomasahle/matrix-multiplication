import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeDataShape20
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

/-!
# Bounded positive beta-three row 124

Each coordinate is checked through a literal midpoint after output regions `0,1,2`.  Keeping all
six bounded three-region reductions in one row module amortizes their common import closure while
staying below the kernel-memory threshold that a single six-region reduction can exceed.
Certificate: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row124

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.TotalQuotientPrimary

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Exact accumulator after output regions `0,1,2`. -/
def row124Coordinate0Middle : Array ℕ := #[51628191252480, 0, 0, 177600169246720, 0, 51628140920832, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row124Coordinate0_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 0 =
        row124Coordinate0Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row124Coordinate0Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row124Coordinate0_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 0
        row124Coordinate0Middle =
          BetaThree.row124Coordinate0 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row124Coordinate0Middle
    BetaThree.row124Coordinate0
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row124Coordinate0_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 0 =
        BetaThree.row124Coordinate0 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 0
      row124Coordinate0Middle
      BetaThree.row124Coordinate0
      row124Coordinate0_firstHalf_eq
      row124Coordinate0_secondHalf_eq

/-- Exact accumulator after output regions `0,1,2`. -/
def row124Coordinate1Middle : Array ℕ := #[3707982839808, 0, 136720267870208, 0, 0, 136720267870208, 0, 0, 0, 0, 0, 0, 3707982839808, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row124Coordinate1_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 1 =
        row124Coordinate1Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row124Coordinate1Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row124Coordinate1_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 1
        row124Coordinate1Middle =
          BetaThree.row124Coordinate1 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row124Coordinate1Middle
    BetaThree.row124Coordinate1
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row124Coordinate1_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 1 =
        BetaThree.row124Coordinate1 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 1
      row124Coordinate1Middle
      BetaThree.row124Coordinate1
      row124Coordinate1_firstHalf_eq
      row124Coordinate1_secondHalf_eq

/-- Exact accumulator after output regions `0,1,2`. -/
def row124Coordinate2Middle : Array ℕ := #[3913486958592, 0, 136514763751424, 0, 0, 136514713419776, 0, 0, 0, 0, 0, 0, 3913537290240, 0, 0, 0, 0, 0, 0]

/-- Bounded reconstruction of the first three regional contributions. -/
opaque row124Coordinate2_firstHalf_eq :
    positiveBetaThreeCoordinateFirstHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 2 =
        row124Coordinate2Middle := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row124Coordinate2Middle
  rfl

/-- Bounded reconstruction of output regions `3,4,5` from the checked midpoint. -/
opaque row124Coordinate2_secondHalf_eq :
    positiveBetaThreeCoordinateSecondHalfFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 2
        row124Coordinate2Middle =
          BetaThree.row124Coordinate2 := by
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData, Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData, EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData, MuData0.data_eq_rawData]
  unfold row124Coordinate2Middle
    BetaThree.row124Coordinate2
  rfl

/-- Assemble both bounded halves into the original six-region coordinate recurrence. -/
theorem row124Coordinate2_eq :
    positiveBetaThreeCoordinateRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 2 =
        BetaThree.row124Coordinate2 :=
  positiveBetaThreeCoordinateRowFor_eq_of_halves
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 2
      row124Coordinate2Middle
      BetaThree.row124Coordinate2
      row124Coordinate2_firstHalf_eq
      row124Coordinate2_secondHalf_eq


/-- Assemble this global beta-three row from its three bounded coordinate checks. -/
theorem row124_eq :
    betaThreeGlobalRowFor MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables 124 = BetaThree.row124 := by
  unfold BetaThree.row124
  apply betaThreeGlobalRowFor_eq_of_positive
  · decide
  · exact row124Coordinate0_eq
  · exact row124Coordinate1_eq
  · exact row124Coordinate2_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.Row124
