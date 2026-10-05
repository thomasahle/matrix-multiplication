import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk7
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 8; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk8

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
    ⟨156954672, 63, 2⟩,
    ⟨2289750120, 68, 1⟩,
    ⟨150000984, 82, 0⟩,
    ⟨69426, 213, 2⟩,
    ⟨533988, 178, 1⟩,
    ⟨71442, 174, 0⟩,
    ⟨121968, 67, 2⟩,
    ⟨1091160, 82, 1⟩,
    ⟨130536, 67, 0⟩,
    ⟨209664, 224, 2⟩,
    ⟨2316384, 170, 1⟩,
    ⟨213192, 217, 0⟩,
    ⟨6504120, 100, 2⟩,
    ⟨84261240, 41, 1⟩,
    ⟨5700240, 79, 0⟩,
    ⟨138852, 203, 2⟩,
    ⟨1072512, 170, 1⟩,
    ⟨142884, 195, 0⟩,
    ⟨49224, 63, 2⟩,
    ⟨337008, 68, 1⟩,
    ⟨51072, 82, 0⟩,
    ⟨50232, 213, 2⟩,
    ⟨339864, 178, 1⟩,
    ⟨51492, 174, 0⟩,
    ⟨51176664, 67, 2⟩,
    ⟨770325864, 82, 1⟩,
    ⟨52681860, 66, 0⟩,
    ⟨52752, 224, 2⟩,
    ⟨344400, 170, 1⟩,
    ⟨53088, 217, 0⟩,
    ⟨1607172, 100, 2⟩,
    ⟨20559336, 41, 1⟩,
    ⟨1353408, 79, 0⟩,
    ⟨50232, 203, 2⟩,
    ⟨340536, 171, 1⟩,
    ⟨51408, 195, 0⟩,
    ⟨53629632, 68, 1⟩,
    ⟨1670832, 82, 0⟩,
    ⟨327840, 178, 1⟩,
    ⟨33720, 174, 0⟩,
    ⟨544884, 82, 1⟩,
    ⟨45696, 67, 0⟩,
    ⟨335280, 170, 1⟩,
    ⟨34560, 218, 0⟩,
    ⟨73802592, 41, 1⟩,
    ⟨2595504, 79, 0⟩,
    ⟨329640, 171, 1⟩,
    ⟨33240, 195, 0⟩,
    ⟨19400458392, 68, 1⟩,
    ⟨221466420, 82, 0⟩,
    ⟨52535756, 177, 1⟩,
    ⟨2080624, 173, 0⟩,
    ⟨187100113200, 81, 1⟩,
    ⟨1573471900, 66, 0⟩,
    ⟨53436026, 170, 1⟩,
    ⟨2220666, 216, 0⟩,
    ⟨7792056916, 41, 1⟩,
    ⟨101350396, 79, 0⟩,
    ⟨52655792, 170, 1⟩,
    ⟨2080624, 194, 0⟩,
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
    ⟨137305152, 68, 1⟩,
    ⟨3648960, 82, 0⟩,
    ⟨524928, 178, 1⟩,
    ⟨50496, 174, 0⟩,
    ⟨905184, 82, 1⟩,
    ⟨74256, 67, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 720 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk8
