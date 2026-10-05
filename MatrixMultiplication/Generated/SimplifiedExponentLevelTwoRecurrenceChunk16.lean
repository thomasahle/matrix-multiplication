import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk15
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 16; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk16

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
    ⟨1472064, 63, 2⟩,
    ⟨43793904, 82, 0⟩,
    ⟨59856, 213, 2⟩,
    ⟨909672, 173, 0⟩,
    ⟨2725512, 67, 2⟩,
    ⟨82969656, 67, 0⟩,
    ⟨32160, 224, 2⟩,
    ⟨323280, 217, 0⟩,
    ⟨32868, 100, 2⟩,
    ⟨358116, 79, 0⟩,
    ⟨34980, 203, 2⟩,
    ⟨355608, 195, 0⟩,
    ⟨246955776, 63, 2⟩,
    ⟨10063447872, 82, 0⟩,
    ⟨5029296, 213, 2⟩,
    ⟨113289228, 171, 0⟩,
    ⟨5089560840, 67, 2⟩,
    ⟨220886940456, 67, 0⟩,
    ⟨2492970, 224, 2⟩,
    ⟨57078174, 215, 0⟩,
    ⟨2666394, 100, 2⟩,
    ⟨58704024, 78, 0⟩,
    ⟨2558004, 203, 2⟩,
    ⟨56362800, 193, 0⟩,
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
    ⟨66456, 63, 2⟩,
    ⟨835224, 82, 0⟩,
    ⟨70200, 213, 2⟩,
    ⟨839280, 173, 0⟩,
    ⟨90720, 67, 2⟩,
    ⟨1170720, 67, 0⟩,
    ⟨62040, 224, 2⟩,
    ⟨708576, 217, 0⟩,
    ⟨6334416, 100, 2⟩,
    ⟨258559344, 78, 0⟩,
    ⟨135072, 203, 2⟩,
    ⟨2589552, 194, 0⟩,
    ⟨881760, 63, 2⟩,
    ⟨28943772, 82, 0⟩,
    ⟨17760, 213, 2⟩,
    ⟨164220, 173, 0⟩,
    ⟨1076988, 67, 2⟩,
    ⟨34516152, 67, 0⟩,
    ⟨24738, 224, 2⟩,
    ⟨305748, 217, 0⟩,
    ⟨18414, 100, 2⟩,
    ⟨180180, 79, 0⟩,
    ⟨31320, 203, 2⟩,
    ⟨469620, 194, 0⟩,
    ⟨46656, 68, 1⟩,
    ⟨508032, 82, 0⟩,
    ⟨90720, 178, 1⟩,
    ⟨1670544, 173, 0⟩,
    ⟨3915336, 82, 1⟩,
    ⟨124526784, 66, 0⟩,
    ⟨42168, 171, 1⟩,
    ⟨442008, 217, 0⟩,
    ⟨47736, 41, 1⟩,
    ⟨519996, 79, 0⟩,
    ⟨42624, 171, 1⟩,
    ⟨506304, 195, 0⟩,
    ⟨640838280, 68, 1⟩,
    ⟨27812381352, 82, 0⟩,
    ⟨4874980, 177, 1⟩,
    ⟨114429076, 171, 0⟩,
    ⟨4792991700, 82, 1⟩,
    ⟨208335372560, 67, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 1440 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk16
