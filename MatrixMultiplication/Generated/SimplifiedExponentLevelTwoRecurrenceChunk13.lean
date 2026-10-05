import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk12
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 13; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk13

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
    ⟨1354500, 170, 1⟩,
    ⟨291480, 217, 0⟩,
    ⟨1356600, 41, 1⟩,
    ⟨291900, 79, 0⟩,
    ⟨2239104, 170, 1⟩,
    ⟨411936, 195, 0⟩,
    ⟨368630400, 68, 1⟩,
    ⟨61724160, 82, 0⟩,
    ⟨1286220, 177, 1⟩,
    ⟨249210, 173, 0⟩,
    ⟨560520, 82, 1⟩,
    ⟨137700, 67, 0⟩,
    ⟨453450, 170, 1⟩,
    ⟨125550, 217, 0⟩,
    ⟨49723980, 41, 1⟩,
    ⟨9643080, 79, 0⟩,
    ⟨664440, 170, 1⟩,
    ⟨154560, 195, 0⟩,
    ⟨106092, 63, 2⟩,
    ⟨382158, 82, 0⟩,
    ⟨404460, 213, 2⟩,
    ⟨2090340, 172, 0⟩,
    ⟨82858650, 67, 2⟩,
    ⟨495134472, 67, 0⟩,
    ⟨137088, 224, 2⟩,
    ⟨514584, 217, 0⟩,
    ⟨14197302, 100, 2⟩,
    ⟨93637782, 78, 0⟩,
    ⟨138768, 203, 2⟩,
    ⟨512568, 194, 0⟩,
    ⟨22510391288, 63, 2⟩,
    ⟨144434703952, 82, 0⟩,
    ⟨54775292, 213, 2⟩,
    ⟨337078720, 171, 0⟩,
    ⟨208406757680, 67, 2⟩,
    ⟨1223132074384, 69, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨55167244, 100, 2⟩,
    ⟨337470672, 78, 0⟩,
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
    ⟨0, 0, 2⟩,
    ⟨0, 0, 0⟩,
    ⟨163052736, 63, 2⟩,
    ⟨1051659840, 82, 0⟩,
    ⟨256368, 213, 2⟩,
    ⟨1057056, 173, 0⟩,
    ⟨264768, 67, 2⟩,
    ⟨1048656, 67, 0⟩,
    ⟨350784, 224, 2⟩,
    ⟨1631952, 216, 0⟩,
    ⟨20415024, 100, 2⟩,
    ⟨138632256, 78, 0⟩,
    ⟨191268, 203, 2⟩,
    ⟨792288, 194, 0⟩,
    ⟨135180, 63, 2⟩,
    ⟨567900, 82, 0⟩,
    ⟨530640, 213, 2⟩,
    ⟨3413520, 172, 0⟩,
    ⟨64156500, 67, 2⟩,
    ⟨421496100, 67, 0⟩,
    ⟨133560, 224, 2⟩,
    ⟨569340, 217, 0⟩,
    ⟨130680, 100, 2⟩,
    ⟨573300, 79, 0⟩,
    ⟨197100, 203, 2⟩,
    ⟨984900, 194, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 1170 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk13
