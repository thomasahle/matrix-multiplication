import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk8
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 9; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk9

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
    ⟨602208, 170, 1⟩,
    ⟨57888, 218, 0⟩,
    ⟨118601568, 41, 1⟩,
    ⟨3752928, 79, 0⟩,
    ⟨589248, 171, 1⟩,
    ⟨55080, 195, 0⟩,
    ⟨25547820, 68, 1⟩,
    ⟨815976, 82, 0⟩,
    ⟨177342, 178, 1⟩,
    ⟨19008, 174, 0⟩,
    ⟨238950, 82, 1⟩,
    ⟨23310, 67, 0⟩,
    ⟨297108, 170, 1⟩,
    ⟨27000, 218, 0⟩,
    ⟨38030244, 41, 1⟩,
    ⟨1366008, 79, 0⟩,
    ⟨180444, 171, 1⟩,
    ⟨19140, 195, 0⟩,
    ⟨500018148, 63, 2⟩,
    ⟨75189618, 82, 0⟩,
    ⟨786744, 213, 2⟩,
    ⟨195804, 173, 0⟩,
    ⟨919926, 67, 2⟩,
    ⟨228438, 67, 0⟩,
    ⟨1788150, 224, 2⟩,
    ⟨366366, 217, 0⟩,
    ⟨95148144, 100, 2⟩,
    ⟨11966976, 78, 0⟩,
    ⟨1496880, 203, 2⟩,
    ⟨322476, 195, 0⟩,
    ⟨1217881046960, 63, 2⟩,
    ⟨192966642960, 83, 0⟩,
    ⟨316596596, 213, 2⟩,
    ⟨53660440, 171, 0⟩,
    ⟨316134006, 67, 2⟩,
    ⟨54308066, 67, 0⟩,
    ⟨320297316, 224, 2⟩,
    ⟨50514828, 215, 0⟩,
    ⟨88177795584, 100, 2⟩,
    ⟨12129479872, 78, 0⟩,
    ⟨316596596, 203, 2⟩,
    ⟨53660440, 193, 0⟩,
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
    ⟨1309980, 63, 2⟩,
    ⟨334320, 82, 0⟩,
    ⟨1316700, 213, 2⟩,
    ⟨327180, 173, 0⟩,
    ⟨1594152, 67, 2⟩,
    ⟨385056, 67, 0⟩,
    ⟨1596168, 224, 2⟩,
    ⟨381024, 217, 0⟩,
    ⟨1192851240, 100, 2⟩,
    ⟨171672480, 78, 0⟩,
    ⟨5325852, 203, 2⟩,
    ⟨1008672, 194, 0⟩,
    ⟨125691090, 63, 2⟩,
    ⟨20771760, 82, 0⟩,
    ⟨440700, 213, 2⟩,
    ⟨137250, 173, 0⟩,
    ⟨282973500, 67, 2⟩,
    ⟨47589120, 67, 0⟩,
    ⟨444600, 224, 2⟩,
    ⟨134400, 217, 0⟩,
    ⟨11301120, 100, 2⟩,
    ⟨1665360, 79, 0⟩,
    ⟨441750, 203, 2⟩,
    ⟨135900, 195, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 810 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk9
