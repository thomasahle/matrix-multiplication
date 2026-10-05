import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk10
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 11; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk11

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
    ⟨329986800, 63, 2⟩,
    ⟨171943200, 68, 1⟩,
    ⟨329986800, 82, 0⟩,
    ⟨446220, 213, 2⟩,
    ⟨213120, 178, 1⟩,
    ⟨446220, 173, 0⟩,
    ⟨608975640, 67, 2⟩,
    ⟨315888300, 82, 1⟩,
    ⟨608975640, 67, 0⟩,
    ⟨431280, 224, 2⟩,
    ⟨225180, 170, 1⟩,
    ⟨431280, 217, 0⟩,
    ⟨4111560, 100, 2⟩,
    ⟨2183760, 41, 1⟩,
    ⟨4111560, 79, 0⟩,
    ⟨1146150, 203, 2⟩,
    ⟨541800, 171, 1⟩,
    ⟨1146150, 194, 0⟩,
    ⟨62115700, 63, 2⟩,
    ⟨127948560, 68, 1⟩,
    ⟨127948560, 82, 0⟩,
    ⟨314364, 213, 2⟩,
    ⟨663836, 178, 1⟩,
    ⟨663836, 173, 0⟩,
    ⟨622794882, 67, 2⟩,
    ⟨1279346910, 82, 1⟩,
    ⟨1279346910, 66, 0⟩,
    ⟨308468, 224, 2⟩,
    ⟨668124, 170, 1⟩,
    ⟨668124, 217, 0⟩,
    ⟨11700880, 100, 2⟩,
    ⟨26584796, 41, 1⟩,
    ⟨26584796, 79, 0⟩,
    ⟨313828, 203, 2⟩,
    ⟨664372, 171, 1⟩,
    ⟨664372, 194, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨1447699704720, 67, 2⟩,
    ⟨2805738249480, 79, 1⟩,
    ⟨2805738249480, 70, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨1950527232, 100, 2⟩,
    ⟨4257154008, 41, 1⟩,
    ⟨4257154008, 79, 0⟩,
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
    ⟨0, 0, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 990 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk11
