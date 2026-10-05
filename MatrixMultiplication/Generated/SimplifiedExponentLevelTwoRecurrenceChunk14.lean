import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk13
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 14; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk14

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
    ⟨79401504, 63, 2⟩,
    ⟨85263360, 68, 1⟩,
    ⟨1222996320, 82, 0⟩,
    ⟨92232, 213, 2⟩,
    ⟨99456, 178, 1⟩,
    ⟨694512, 173, 0⟩,
    ⟨24635856, 67, 2⟩,
    ⟨23186688, 82, 1⟩,
    ⟨350546112, 67, 0⟩,
    ⟨92400, 224, 2⟩,
    ⟨101976, 171, 1⟩,
    ⟨693168, 216, 0⟩,
    ⟨133056, 100, 2⟩,
    ⟨151956, 41, 1⟩,
    ⟨1010520, 79, 0⟩,
    ⟨276696, 203, 2⟩,
    ⟨303912, 171, 1⟩,
    ⟨3427704, 193, 0⟩,
    ⟨147745957608, 63, 2⟩,
    ⟨158690102616, 68, 1⟩,
    ⟨2052027189000, 85, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨6087985092, 67, 2⟩,
    ⟨6012357948, 82, 1⟩,
    ⟨86441825592, 67, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨39867682140, 100, 2⟩,
    ⟨78648063858, 41, 1⟩,
    ⟨823448852928, 80, 0⟩,
    ⟨49029462, 203, 2⟩,
    ⟨52714683, 170, 1⟩,
    ⟨729032850, 193, 0⟩,
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
    ⟨123432120, 63, 2⟩,
    ⟨133647192, 68, 1⟩,
    ⟨1959591312, 82, 0⟩,
    ⟨228690, 213, 2⟩,
    ⟨253260, 178, 1⟩,
    ⟨2879100, 172, 0⟩,
    ⟨27971748, 67, 2⟩,
    ⟨26190108, 82, 1⟩,
    ⟨411024348, 67, 0⟩,
    ⟨131544, 224, 2⟩,
    ⟨146916, 171, 1⟩,
    ⟨1069992, 216, 0⟩,
    ⟨128016, 100, 2⟩,
    ⟨147420, 41, 1⟩,
    ⟨1035216, 79, 0⟩,
    ⟨133812, 203, 2⟩,
    ⟨145656, 171, 1⟩,
    ⟨1067976, 194, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 1260 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk14
