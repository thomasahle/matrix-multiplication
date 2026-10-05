import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk11
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 12; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk12

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
    ⟨1053457860, 63, 2⟩,
    ⟨2143071840, 68, 1⟩,
    ⟨2143071840, 82, 0⟩,
    ⟨242760, 213, 2⟩,
    ⟨534240, 177, 1⟩,
    ⟨534240, 173, 0⟩,
    ⟨705600, 67, 2⟩,
    ⟨1662570, 82, 1⟩,
    ⟨1662570, 67, 0⟩,
    ⟨479640, 224, 2⟩,
    ⟨1071420, 170, 1⟩,
    ⟨1071420, 216, 0⟩,
    ⟨43834560, 100, 2⟩,
    ⟨98978880, 41, 1⟩,
    ⟨98978880, 79, 0⟩,
    ⟨244440, 203, 2⟩,
    ⟨532350, 170, 1⟩,
    ⟨532350, 194, 0⟩,
    ⟨447585280, 63, 2⟩,
    ⟨912654360, 68, 1⟩,
    ⟨912654360, 82, 0⟩,
    ⟨1386320, 213, 2⟩,
    ⟨2886676, 177, 1⟩,
    ⟨2886676, 172, 0⟩,
    ⟨388032, 67, 2⟩,
    ⟨896808, 82, 1⟩,
    ⟨896808, 67, 0⟩,
    ⟨296958, 224, 2⟩,
    ⟨654030, 170, 1⟩,
    ⟨654030, 217, 0⟩,
    ⟨374272, 100, 2⟩,
    ⟨909192, 41, 1⟩,
    ⟨909192, 79, 0⟩,
    ⟨615588, 203, 2⟩,
    ⟨1326636, 170, 1⟩,
    ⟨1326636, 194, 0⟩,
    ⟨530077716, 68, 1⟩,
    ⟨89117196, 82, 0⟩,
    ⟨665700, 177, 1⟩,
    ⟨153930, 173, 0⟩,
    ⟨802116, 82, 1⟩,
    ⟨182196, 67, 0⟩,
    ⟨648690, 170, 1⟩,
    ⟨166950, 217, 0⟩,
    ⟨57029448, 41, 1⟩,
    ⟨11046168, 79, 0⟩,
    ⟨657090, 170, 1⟩,
    ⟨159600, 195, 0⟩,
    ⟨324289288, 68, 1⟩,
    ⟨50272329, 82, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨323821203, 82, 1⟩,
    ⟨50459563, 66, 0⟩,
    ⟨318110566, 170, 1⟩,
    ⟨56544668, 215, 0⟩,
    ⟨1331914148356, 41, 1⟩,
    ⟨201166550025, 79, 0⟩,
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
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨1374240, 68, 1⟩,
    ⟨274260, 82, 0⟩,
    ⟨1369200, 177, 1⟩,
    ⟨278460, 173, 0⟩,
    ⟨1179589824, 82, 1⟩,
    ⟨189308448, 66, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 1080 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk12
