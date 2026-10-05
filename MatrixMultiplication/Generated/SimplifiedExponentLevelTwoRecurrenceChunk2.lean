import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk1
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 2; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk2

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
    ⟨123480, 63, 2⟩,
    ⟨532728, 68, 1⟩,
    ⟨752640, 213, 2⟩,
    ⟨5115600, 177, 1⟩,
    ⟨122640, 67, 2⟩,
    ⟨533064, 82, 1⟩,
    ⟨100044, 224, 2⟩,
    ⟨389718, 170, 1⟩,
    ⟨110455800, 100, 2⟩,
    ⟨573690432, 41, 1⟩,
    ⟨123480, 203, 2⟩,
    ⟨531384, 171, 1⟩,
    ⟨1926795600, 63, 2⟩,
    ⟨12367173240, 68, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨189084658950, 67, 2⟩,
    ⟨1416928018770, 80, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨57090240, 100, 2⟩,
    ⟨339171530, 41, 1⟩,
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
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨146029968, 63, 2⟩,
    ⟨911501136, 68, 1⟩,
    ⟨234864, 213, 2⟩,
    ⟨1078896, 177, 1⟩,
    ⟨235872, 67, 2⟩,
    ⟨1079232, 82, 1⟩,
    ⟨187740, 224, 2⟩,
    ⟨795564, 170, 1⟩,
    ⟨49534128, 100, 2⟩,
    ⟨268718688, 41, 1⟩,
    ⟨277620, 203, 2⟩,
    ⟨1371720, 170, 1⟩,
    ⟨112350, 63, 2⟩,
    ⟨472800, 68, 1⟩,
    ⟨111450, 213, 2⟩,
    ⟨473850, 178, 1⟩,
    ⟨67813740, 67, 2⟩,
    ⟨420007680, 82, 1⟩,
    ⟨245520, 224, 2⟩,
    ⟨1173960, 170, 1⟩,
    ⟨139320, 100, 2⟩,
    ⟨563220, 41, 1⟩,
    ⟨293760, 203, 2⟩,
    ⟨1728390, 170, 1⟩,
    ⟨2328336, 63, 2⟩,
    ⟨82246896, 68, 1⟩,
    ⟨31284, 213, 2⟩,
    ⟨350064, 178, 1⟩,
    ⟨1305612, 67, 2⟩,
    ⟨44390808, 82, 1⟩,
    ⟨31212, 224, 2⟩,
    ⟨300996, 170, 1⟩,
    ⟨43740, 100, 2⟩,
    ⟨494640, 41, 1⟩,
    ⟨52728, 203, 2⟩,
    ⟨811512, 170, 1⟩,
    ⟨1270341800, 63, 2⟩,
    ⟨165906639080, 68, 1⟩,
    ⟨1887249, 213, 2⟩,
    ⟨53086488, 177, 1⟩,
    ⟨429034606, 67, 2⟩,
    ⟨51016114968, 82, 1⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree generatedPrimaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 180 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence.Chunk2
