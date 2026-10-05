import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk13
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 14; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk14

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
    ⟨79401504, 63, 2⟩,
    ⟨85263360, 68, 1⟩,
    ⟨1222996320, 82, 0⟩,
    ⟨92232, 213, 2⟩,
    ⟨99456, 178, 1⟩,
    ⟨694512, 173, 0⟩,
    ⟨24635856, 67, 2⟩,
    ⟨23186688, 82, 1⟩,
    ⟨350546112, 67, 0⟩,
    ⟨92400, 224, 2⟩,
    ⟨101976, 171, 1⟩,
    ⟨693168, 216, 0⟩,
    ⟨133056, 100, 2⟩,
    ⟨151956, 41, 1⟩,
    ⟨1010520, 79, 0⟩,
    ⟨276696, 203, 2⟩,
    ⟨303912, 171, 1⟩,
    ⟨3427704, 193, 0⟩,
    ⟨169434800470, 57, 2⟩,
    ⟨150712723070, 64, 1⟩,
    ⟨2145550070040, 75, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨5984118972, 67, 2⟩,
    ⟨5873301954, 82, 1⟩,
    ⟨84959713800, 68, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨38058857746, 96, 2⟩,
    ⟨63644644466, 40, 1⟩,
    ⟨745825682888, 77, 0⟩,
    ⟨48304854, 203, 2⟩,
    ⟨51935611, 170, 1⟩,
    ⟨718258450, 193, 0⟩,
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
    ⟨129309840, 63, 2⟩,
    ⟨140011344, 68, 1⟩,
    ⟨2052905184, 82, 0⟩,
    ⟨239580, 213, 2⟩,
    ⟨265320, 178, 1⟩,
    ⟨3016200, 172, 0⟩,
    ⟨29303736, 67, 2⟩,
    ⟨27437256, 82, 1⟩,
    ⟨430596936, 67, 0⟩,
    ⟨137808, 224, 2⟩,
    ⟨153912, 171, 1⟩,
    ⟨1120944, 216, 0⟩,
    ⟨134112, 100, 2⟩,
    ⟨154440, 41, 1⟩,
    ⟨1084512, 79, 0⟩,
    ⟨140184, 203, 2⟩,
    ⟨152592, 171, 1⟩,
    ⟨1118832, 194, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 1260 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk14
