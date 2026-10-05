import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoMassThreeData
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 0; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk0

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
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨48536250, 63, 2⟩,
    ⟨4382560, 213, 2⟩,
    ⟨45908520, 67, 2⟩,
    ⟨5056800, 224, 2⟩,
    ⟨4258963380, 100, 2⟩,
    ⟨6609960, 203, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨92570400, 63, 2⟩,
    ⟨2798640, 68, 1⟩,
    ⟨1422504, 213, 2⟩,
    ⟨78936, 178, 1⟩,
    ⟨32012400, 67, 2⟩,
    ⟨1075320, 82, 1⟩,
    ⟨299376, 224, 2⟩,
    ⟨32832, 171, 1⟩,
    ⟨357192, 100, 2⟩,
    ⟨36828, 41, 1⟩,
    ⟨327240, 203, 2⟩,
    ⟨33720, 171, 1⟩,
    ⟨215985246522, 63, 2⟩,
    ⟨4009006896, 68, 1⟩,
    ⟨54119577, 213, 2⟩,
    ⟨2373113, 177, 1⟩,
    ⟨6230996700, 67, 2⟩,
    ⟨140076670, 82, 1⟩,
    ⟨52628506, 224, 2⟩,
    ⟨2478118, 170, 1⟩,
    ⟨53951569, 100, 2⟩,
    ⟨2247107, 41, 1⟩,
    ⟨54098576, 203, 2⟩,
    ⟨2163103, 170, 1⟩,
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
    ⟨191282400, 63, 2⟩,
    ⟨6026400, 68, 1⟩,
    ⟨2040192, 213, 2⟩,
    ⟨118800, 178, 1⟩,
    ⟨57855696, 67, 2⟩,
    ⟨2039856, 82, 1⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 0 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk0
