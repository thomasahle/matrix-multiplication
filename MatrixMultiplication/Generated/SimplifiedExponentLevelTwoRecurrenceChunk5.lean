import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk4
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 5; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk5

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
    ⟨610505190432, 63, 2⟩,
    ⟨44221974384, 68, 1⟩,
    ⟨41399295168, 82, 0⟩,
    ⟨666465926, 213, 2⟩,
    ⟨52173582, 177, 1⟩,
    ⟨48636390, 172, 0⟩,
    ⟨2143469376756, 66, 2⟩,
    ⟨145335850130, 81, 1⟩,
    ⟨151899404652, 67, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨671476948, 100, 2⟩,
    ⟨50699752, 41, 1⟩,
    ⟨41856772, 78, 0⟩,
    ⟨670297884, 203, 2⟩,
    ⟨47752092, 170, 1⟩,
    ⟨46573028, 193, 0⟩,
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
    ⟨1515780, 63, 2⟩,
    ⟨212436, 68, 1⟩,
    ⟨205254, 82, 0⟩,
    ⟨2182320, 213, 2⟩,
    ⟨245952, 178, 1⟩,
    ⟨234864, 173, 0⟩,
    ⟨514616256, 67, 2⟩,
    ⟨34550208, 82, 1⟩,
    ⟨38868984, 67, 0⟩,
    ⟨1068480, 224, 2⟩,
    ⟨146664, 170, 1⟩,
    ⟨132300, 217, 0⟩,
    ⟨1836043524, 100, 2⟩,
    ⟨133151256, 41, 1⟩,
    ⟨87430644, 78, 0⟩,
    ⟨1054872, 203, 2⟩,
    ⟨140868, 171, 1⟩,
    ⟨133812, 195, 0⟩,
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
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 450 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk5
