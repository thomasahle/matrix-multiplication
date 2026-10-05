import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk16
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 17; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk17

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
    ⟨5753000, 170, 1⟩,
    ⟨130279300, 215, 0⟩,
    ⟨8551050, 41, 1⟩,
    ⟨201224250, 79, 0⟩,
    ⟨5334600, 170, 1⟩,
    ⟨134411000, 193, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨62400, 68, 1⟩,
    ⟨646800, 82, 0⟩,
    ⟨106920, 178, 1⟩,
    ⟨1685448, 173, 0⟩,
    ⟨3758880, 82, 1⟩,
    ⟨119734080, 66, 0⟩,
    ⟨64320, 171, 1⟩,
    ⟨637920, 217, 0⟩,
    ⟨4087680, 41, 1⟩,
    ⟨130499184, 79, 0⟩,
    ⟨64080, 171, 1⟩,
    ⟨648720, 195, 0⟩,
    ⟨22464, 68, 1⟩,
    ⟨212784, 82, 0⟩,
    ⟨21312, 178, 1⟩,
    ⟨197280, 173, 0⟩,
    ⟨967266, 82, 1⟩,
    ⟨29118042, 66, 0⟩,
    ⟨30096, 171, 1⟩,
    ⟨349140, 217, 0⟩,
    ⟨1048320, 41, 1⟩,
    ⟨33520032, 79, 0⟩,
    ⟨20808, 171, 1⟩,
    ⟨198072, 195, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨79543464, 82, 0⟩,
    ⟨4759326, 172, 0⟩,
    ⟨6614088000, 67, 0⟩,
    ⟨5903040, 215, 0⟩,
    ⟨54234180, 79, 0⟩,
    ⟨10987704, 193, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 1530 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk17
