import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk16
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 17; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk17

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRecurrence
open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedInputs : List EdgeInput :=
  [
    ⟨4874980, 170, 1⟩,
    ⟨110484774, 215, 0⟩,
    ⟨7245993, 41, 1⟩,
    ⟨170513505, 79, 0⟩,
    ⟨4520436, 170, 1⟩,
    ⟨113897260, 193, 0⟩,
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
    ⟨71764616, 82, 0⟩,
    ⟨4293894, 172, 0⟩,
    ⟨5930960000, 67, 0⟩,
    ⟨5325760, 215, 0⟩,
    ⟨48930420, 79, 0⟩,
    ⟨9913176, 193, 0⟩,
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
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 1530 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk17
