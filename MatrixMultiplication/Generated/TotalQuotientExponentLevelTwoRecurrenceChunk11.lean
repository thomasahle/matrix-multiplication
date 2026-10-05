import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk10
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 11; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk11

open MatrixMultiplication.Generated.TotalQuotientPrimary
open MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence
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
    ⟨64897000, 63, 2⟩,
    ⟨133677600, 68, 1⟩,
    ⟨133677600, 82, 0⟩,
    ⟨328440, 213, 2⟩,
    ⟨693560, 178, 1⟩,
    ⟨693560, 173, 0⟩,
    ⟨650681220, 67, 2⟩,
    ⟨1336631100, 82, 1⟩,
    ⟨1336631100, 66, 0⟩,
    ⟨322280, 224, 2⟩,
    ⟨698040, 170, 1⟩,
    ⟨698040, 217, 0⟩,
    ⟨12224800, 100, 2⟩,
    ⟨27775160, 41, 1⟩,
    ⟨27775160, 79, 0⟩,
    ⟨327880, 203, 2⟩,
    ⟨694120, 171, 1⟩,
    ⟨694120, 194, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨1383788325860, 78, 2⟩,
    ⟨2702481904980, 58, 1⟩,
    ⟨2702481904980, 75, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨1879065960, 100, 2⟩,
    ⟨4081577700, 41, 1⟩,
    ⟨4081577700, 79, 0⟩,
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
    edgeInputRangeWithMassThree MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 990 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk11
