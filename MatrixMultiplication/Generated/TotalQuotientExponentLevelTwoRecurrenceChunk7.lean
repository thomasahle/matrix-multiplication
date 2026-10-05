import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk6
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 7; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk7

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
    ⟨51007460, 63, 2⟩,
    ⟨51007460, 68, 1⟩,
    ⟨25562812, 82, 0⟩,
    ⟨637260, 213, 2⟩,
    ⟨637260, 178, 1⟩,
    ⟨309084, 173, 0⟩,
    ⟨824778528, 67, 2⟩,
    ⟨824778528, 82, 1⟩,
    ⟨421354248, 67, 0⟩,
    ⟨650934, 224, 2⟩,
    ⟨650934, 170, 1⟩,
    ⟨287670, 217, 0⟩,
    ⟨30116340, 100, 2⟩,
    ⟨30116340, 41, 1⟩,
    ⟨14907240, 79, 0⟩,
    ⟨635712, 203, 2⟩,
    ⟨635712, 171, 1⟩,
    ⟨304698, 195, 0⟩,
    ⟨116100, 63, 2⟩,
    ⟨1135200, 68, 1⟩,
    ⟨122034, 82, 0⟩,
    ⟨130548, 213, 2⟩,
    ⟨1110948, 177, 1⟩,
    ⟨133902, 173, 0⟩,
    ⟨106921908, 67, 2⟩,
    ⟨1605925128, 82, 1⟩,
    ⟨112512596, 66, 0⟩,
    ⟨138288, 224, 2⟩,
    ⟨1127976, 170, 1⟩,
    ⟨139062, 217, 0⟩,
    ⟨128484, 100, 2⟩,
    ⟨1123332, 41, 1⟩,
    ⟨133644, 79, 0⟩,
    ⟨549024, 203, 2⟩,
    ⟨8350944, 170, 1⟩,
    ⟨552636, 195, 0⟩,
    ⟨176114311296, 67, 2⟩,
    ⟨2557088312064, 62, 1⟩,
    ⟨194411902080, 81, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨176626304, 100, 2⟩,
    ⟨2570024512, 41, 1⟩,
    ⟨196189344, 79, 0⟩,
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
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 630 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk7
