import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk3
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 4; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk4

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
    ⟨104198472, 63, 2⟩,
    ⟨3065832, 82, 0⟩,
    ⟨425724, 213, 2⟩,
    ⟨38688, 174, 0⟩,
    ⟨486000, 67, 2⟩,
    ⟨41400, 67, 0⟩,
    ⟨366036, 224, 2⟩,
    ⟨33396, 218, 0⟩,
    ⟨22923264, 100, 2⟩,
    ⟨733824, 79, 0⟩,
    ⟨360624, 203, 2⟩,
    ⟨34056, 195, 0⟩,
    ⟨214840525900, 63, 2⟩,
    ⟨3981600480, 82, 0⟩,
    ⟨52836212, 213, 2⟩,
    ⟨2274272, 172, 0⟩,
    ⟨159848832, 67, 2⟩,
    ⟨6396390, 67, 0⟩,
    ⟨212075864, 224, 2⟩,
    ⟨6741592, 215, 0⟩,
    ⟨53587534, 100, 2⟩,
    ⟨2213354, 78, 0⟩,
    ⟨106037932, 203, 2⟩,
    ⟨4589156, 194, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨45556728, 63, 2⟩,
    ⟨1605216, 82, 0⟩,
    ⟨699072, 213, 2⟩,
    ⟨58344, 174, 0⟩,
    ⟨198404064, 67, 2⟩,
    ⟨6567648, 67, 0⟩,
    ⟨329160, 224, 2⟩,
    ⟨35880, 218, 0⟩,
    ⟨10406880, 100, 2⟩,
    ⟨411840, 79, 0⟩,
    ⟨388224, 203, 2⟩,
    ⟨42192, 195, 0⟩,
    ⟨284796, 63, 2⟩,
    ⟨26892, 82, 0⟩,
    ⟨270810, 213, 2⟩,
    ⟨26418, 174, 0⟩,
    ⟨504768, 67, 2⟩,
    ⟨39360, 67, 0⟩,
    ⟨275298, 224, 2⟩,
    ⟨26112, 218, 0⟩,
    ⟨61730424, 100, 2⟩,
    ⟨1754244, 78, 0⟩,
    ⟨945012, 203, 2⟩,
    ⟨54900, 195, 0⟩,
    ⟨360437952, 63, 2⟩,
    ⟨23094960, 68, 1⟩,
    ⟨21607488, 82, 0⟩,
    ⟨4220832, 213, 2⟩,
    ⟨336336, 178, 1⟩,
    ⟨328020, 173, 0⟩,
    ⟨666288, 67, 2⟩,
    ⟨102312, 82, 1⟩,
    ⟨101976, 67, 0⟩,
    ⟨706608, 224, 2⟩,
    ⟨104664, 171, 1⟩,
    ⟨95760, 217, 0⟩,
    ⟨1224988632, 100, 2⟩,
    ⟨79304400, 41, 1⟩,
    ⟨52605252, 78, 0⟩,
    ⟨696864, 203, 2⟩,
    ⟨100800, 171, 1⟩,
    ⟨96600, 195, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 360 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk4
