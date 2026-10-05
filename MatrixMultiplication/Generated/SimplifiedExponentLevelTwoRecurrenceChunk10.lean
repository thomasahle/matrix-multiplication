import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk9
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 10; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk10

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
    ⟨269199488, 63, 2⟩,
    ⟨140059328, 68, 1⟩,
    ⟨269199488, 82, 0⟩,
    ⟨1042848, 213, 2⟩,
    ⟨476544, 178, 1⟩,
    ⟨1042848, 173, 0⟩,
    ⟨1009498080, 67, 2⟩,
    ⟨523647600, 82, 1⟩,
    ⟨1009498080, 67, 0⟩,
    ⟨654704, 224, 2⟩,
    ⟨339456, 170, 1⟩,
    ⟨654704, 217, 0⟩,
    ⟨145431328, 100, 2⟩,
    ⟨79545312, 41, 1⟩,
    ⟨145431328, 78, 0⟩,
    ⟨665312, 203, 2⟩,
    ⟨328848, 171, 1⟩,
    ⟨665312, 194, 0⟩,
    ⟨753156128520, 63, 2⟩,
    ⟨383870435760, 68, 1⟩,
    ⟨753156128520, 83, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨1537723952640, 66, 2⟩,
    ⟨757069614720, 81, 1⟩,
    ⟨1537723952640, 69, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨462870954000, 100, 2⟩,
    ⟨245604996000, 41, 1⟩,
    ⟨462870954000, 79, 0⟩,
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
    ⟨0, 0, 0⟩,
    ⟨605902752, 63, 2⟩,
    ⟨315958656, 68, 1⟩,
    ⟨605902752, 82, 0⟩,
    ⟨1057472, 213, 2⟩,
    ⟨485888, 178, 1⟩,
    ⟨1057472, 173, 0⟩,
    ⟨1572043200, 67, 2⟩,
    ⟨816088000, 82, 1⟩,
    ⟨1572043200, 67, 0⟩,
    ⟨1023776, 224, 2⟩,
    ⟨516672, 170, 1⟩,
    ⟨1023776, 216, 0⟩,
    ⟨1580592, 100, 2⟩,
    ⟨783744, 41, 1⟩,
    ⟨1580592, 79, 0⟩,
    ⟨1045824, 203, 2⟩,
    ⟨495040, 171, 1⟩,
    ⟨1045824, 194, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 900 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk10
