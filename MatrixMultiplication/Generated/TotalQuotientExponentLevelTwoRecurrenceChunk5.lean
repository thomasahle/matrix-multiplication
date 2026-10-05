import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk4
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 5; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk5

open MatrixMultiplication.Generated.TotalQuotientPrimary
open MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRecurrence
open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedInputs : List EdgeInput :=
  [
    ⟨588212348160, 67, 2⟩,
    ⟨41811749220, 67, 1⟩,
    ⟨42847334340, 82, 0⟩,
    ⟨669753420, 213, 2⟩,
    ⟨52430940, 177, 1⟩,
    ⟨48876300, 172, 0⟩,
    ⟨2172146306040, 68, 2⟩,
    ⟨143983359180, 75, 1⟩,
    ⟨170682260220, 69, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨674789160, 100, 2⟩,
    ⟨50949840, 41, 1⟩,
    ⟨42063240, 78, 0⟩,
    ⟨673604280, 203, 2⟩,
    ⟨47987640, 170, 1⟩,
    ⟨46802760, 193, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨1587960, 63, 2⟩,
    ⟨222552, 68, 1⟩,
    ⟨215028, 82, 0⟩,
    ⟨2286240, 213, 2⟩,
    ⟨257664, 178, 1⟩,
    ⟨246048, 173, 0⟩,
    ⟨539121792, 67, 2⟩,
    ⟨36195456, 82, 1⟩,
    ⟨40719888, 67, 0⟩,
    ⟨1119360, 224, 2⟩,
    ⟨153648, 170, 1⟩,
    ⟨138600, 217, 0⟩,
    ⟨1924314480, 100, 2⟩,
    ⟨139491792, 41, 1⟩,
    ⟨91594008, 78, 0⟩,
    ⟨1105104, 203, 2⟩,
    ⟨147576, 171, 1⟩,
    ⟨140184, 195, 0⟩,
    ⟨160806240, 63, 2⟩,
    ⟨11148480, 68, 1⟩,
    ⟨10654560, 82, 0⟩,
    ⟨489636, 213, 2⟩,
    ⟨82278, 178, 1⟩,
    ⟨80388, 173, 0⟩,
    ⟨421217160, 67, 2⟩,
    ⟨27753180, 82, 1⟩,
    ⟨31187520, 67, 0⟩,
    ⟨498708, 224, 2⟩,
    ⟨84294, 171, 1⟩,
    ⟨78498, 217, 0⟩,
    ⟨199633056, 100, 2⟩,
    ⟨13923840, 41, 1⟩,
    ⟨10094784, 78, 0⟩,
    ⟨664272, 203, 2⟩,
    ⟨107184, 171, 1⟩,
    ⟨103824, 195, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 450 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk5
