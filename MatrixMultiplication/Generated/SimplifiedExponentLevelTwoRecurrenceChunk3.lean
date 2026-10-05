import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk2
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 3; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk3

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
    ⟨2049593, 224, 2⟩,
    ⟨54283775, 170, 1⟩,
    ⟨1907542, 100, 2⟩,
    ⟨55602820, 41, 1⟩,
    ⟨2759848, 203, 2⟩,
    ⟨105280084, 170, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨4307160, 63, 2⟩,
    ⟨173412888, 68, 1⟩,
    ⟨81144, 213, 2⟩,
    ⟨1424160, 177, 1⟩,
    ⟨2167200, 67, 2⟩,
    ⟨81177120, 81, 1⟩,
    ⟨47040, 224, 2⟩,
    ⟨475104, 170, 1⟩,
    ⟨55728, 100, 2⟩,
    ⟨606960, 41, 1⟩,
    ⟨38880, 203, 2⟩,
    ⟨393120, 171, 1⟩,
    ⟨1244880, 63, 2⟩,
    ⟨41751360, 68, 1⟩,
    ⟨18348, 213, 2⟩,
    ⟨177144, 178, 1⟩,
    ⟨678468, 67, 2⟩,
    ⟨21661332, 81, 1⟩,
    ⟨19734, 224, 2⟩,
    ⟨184074, 170, 1⟩,
    ⟨31284, 100, 2⟩,
    ⟨361152, 41, 1⟩,
    ⟨21528, 203, 2⟩,
    ⟨210600, 171, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨61458072, 68, 1⟩,
    ⟨27852132, 177, 1⟩,
    ⟨349703664, 81, 1⟩,
    ⟨472328192, 170, 1⟩,
    ⟨4419104, 41, 1⟩,
    ⟨50505648, 170, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 270 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk3
