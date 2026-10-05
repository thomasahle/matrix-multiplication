import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk5
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 6; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk6

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
    ⟨69465600, 63, 2⟩,
    ⟨69465600, 68, 1⟩,
    ⟨34786400, 82, 0⟩,
    ⟨657672, 213, 2⟩,
    ⟨657672, 178, 1⟩,
    ⟨324012, 173, 0⟩,
    ⟨1314115488, 67, 2⟩,
    ⟨1314115488, 82, 1⟩,
    ⟨671851746, 67, 0⟩,
    ⟨678308, 224, 2⟩,
    ⟨678308, 170, 1⟩,
    ⟨299088, 217, 0⟩,
    ⟨28872712, 100, 2⟩,
    ⟨28872712, 41, 1⟩,
    ⟨14280648, 79, 0⟩,
    ⟨662496, 203, 2⟩,
    ⟨662496, 171, 1⟩,
    ⟨316508, 195, 0⟩,
    ⟨6782974160, 63, 2⟩,
    ⟨6782974160, 68, 1⟩,
    ⟨3428236940, 82, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨2713755611844, 66, 2⟩,
    ⟨2713755611844, 79, 1⟩,
    ⟨1461912580788, 69, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨2038829733, 100, 2⟩,
    ⟨2038829733, 41, 1⟩,
    ⟨1025321094, 79, 0⟩,
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
    ⟨0, 0, 0⟩,
    ⟨1635504, 63, 2⟩,
    ⟨1635504, 68, 1⟩,
    ⟨708864, 82, 0⟩,
    ⟨3184896, 213, 2⟩,
    ⟨3184896, 177, 1⟩,
    ⟨1589952, 173, 0⟩,
    ⟨2183328576, 67, 2⟩,
    ⟨2183328576, 82, 1⟩,
    ⟨1117959232, 67, 0⟩,
    ⟨2187328, 224, 2⟩,
    ⟨2187328, 170, 1⟩,
    ⟨940992, 216, 0⟩,
    ⟨1647360, 100, 2⟩,
    ⟨1647360, 41, 1⟩,
    ⟨697632, 79, 0⟩,
    ⟨1064544, 203, 2⟩,
    ⟨1064544, 170, 1⟩,
    ⟨481728, 195, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 540 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk6
