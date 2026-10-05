import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk0
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 1; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk1

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
    ⟨522240, 224, 2⟩,
    ⟨56832, 171, 1⟩,
    ⟨695640, 100, 2⟩,
    ⟨69432, 41, 1⟩,
    ⟨643200, 203, 2⟩,
    ⟨62640, 171, 1⟩,
    ⟨346104, 63, 2⟩,
    ⟨31680, 68, 1⟩,
    ⟨665124, 213, 2⟩,
    ⟨43086, 178, 1⟩,
    ⟨61393680, 67, 2⟩,
    ⟨1951272, 82, 1⟩,
    ⟨272850, 224, 2⟩,
    ⟨27234, 171, 1⟩,
    ⟨419094, 100, 2⟩,
    ⟨37422, 41, 1⟩,
    ⟨332010, 203, 2⟩,
    ⟨30366, 171, 1⟩,
    ⟨383166, 63, 2⟩,
    ⟨105336, 68, 1⟩,
    ⟨513576, 213, 2⟩,
    ⟨138432, 178, 1⟩,
    ⟨65965284, 67, 2⟩,
    ⟨9579864, 82, 1⟩,
    ⟨510552, 224, 2⟩,
    ⟨140784, 170, 1⟩,
    ⟨539715792, 100, 2⟩,
    ⟨66740688, 41, 1⟩,
    ⟨1068816, 203, 2⟩,
    ⟨248976, 171, 1⟩,
    ⟨1362647455344, 63, 2⟩,
    ⟨213407664120, 68, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨33351782184, 67, 2⟩,
    ⟨5387446512, 82, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨337061466, 203, 2⟩,
    ⟨58236786, 170, 1⟩,
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
    ⟨120153264, 63, 2⟩,
    ⟨20540520, 68, 1⟩,
    ⟨2479680, 213, 2⟩,
    ⟨506520, 178, 1⟩,
    ⟨752976, 67, 2⟩,
    ⟨222516, 82, 1⟩,
    ⟨498456, 224, 2⟩,
    ⟨150024, 170, 1⟩,
    ⟨1073287152, 100, 2⟩,
    ⟨149989728, 41, 1⟩,
    ⟨1316280, 203, 2⟩,
    ⟨330120, 171, 1⟩,
    ⟨836190, 63, 2⟩,
    ⟨217080, 68, 1⟩,
    ⟨1447200, 213, 2⟩,
    ⟨324000, 178, 1⟩,
    ⟨414569220, 67, 2⟩,
    ⟨71803680, 82, 1⟩,
    ⟨833220, 224, 2⟩,
    ⟨219510, 170, 1⟩,
    ⟨844290, 100, 2⟩,
    ⟨209250, 41, 1⟩,
    ⟨1029930, 203, 2⟩,
    ⟨260700, 171, 1⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 90 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk1
