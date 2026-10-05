import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk14
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 15; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk15

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
    ⟨100380, 63, 2⟩,
    ⟨107940, 68, 1⟩,
    ⟨906780, 82, 0⟩,
    ⟨234192, 213, 2⟩,
    ⟨248472, 178, 1⟩,
    ⟨3305820, 172, 0⟩,
    ⟨51458988, 67, 2⟩,
    ⟨47710320, 82, 1⟩,
    ⟨790287372, 67, 0⟩,
    ⟨101220, 224, 2⟩,
    ⟨111930, 171, 1⟩,
    ⟨924840, 216, 0⟩,
    ⟨95340, 100, 2⟩,
    ⟨108990, 41, 1⟩,
    ⟨909300, 79, 0⟩,
    ⟨125832, 203, 2⟩,
    ⟨137592, 171, 1⟩,
    ⟨1327704, 194, 0⟩,
    ⟨37364166, 68, 1⟩,
    ⟨227018610, 82, 0⟩,
    ⟨481572, 178, 1⟩,
    ⟨2511432, 172, 0⟩,
    ⟨60544344, 82, 1⟩,
    ⟨360123624, 66, 0⟩,
    ⟨174720, 170, 1⟩,
    ⟨638820, 216, 0⟩,
    ⟨169890, 41, 1⟩,
    ⟨644280, 79, 0⟩,
    ⟨172620, 171, 1⟩,
    ⟨642180, 194, 0⟩,
    ⟨47122399618, 66, 1⟩,
    ⟨285232051398, 80, 0⟩,
    ⟨59783704, 177, 1⟩,
    ⟨361228296, 171, 0⟩,
    ⟨194625427360, 72, 1⟩,
    ⟨1193470924204, 75, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨60099463, 41, 1⟩,
    ⟨359333742, 79, 0⟩,
    ⟨60520475, 170, 1⟩,
    ⟨360070513, 193, 0⟩,
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
    ⟨257040, 68, 1⟩,
    ⟨1051344, 82, 0⟩,
    ⟨255696, 178, 1⟩,
    ⟨1052016, 173, 0⟩,
    ⟨74573352, 82, 1⟩,
    ⟨462007308, 66, 0⟩,
    ⟨256704, 170, 1⟩,
    ⟨1050672, 216, 0⟩,
    ⟨111183744, 41, 1⟩,
    ⟨721858368, 79, 0⟩,
    ⟨320460, 171, 1⟩,
    ⟨1316700, 194, 0⟩,
    ⟨11701620, 68, 1⟩,
    ⟨81771480, 82, 0⟩,
    ⟨78210, 178, 1⟩,
    ⟨268560, 173, 0⟩,
    ⟨78390, 82, 1⟩,
    ⟨268470, 67, 0⟩,
    ⟨78480, 171, 1⟩,
    ⟨267930, 217, 0⟩,
    ⟨49607640, 41, 1⟩,
    ⟨344091240, 79, 0⟩,
    ⟨291360, 171, 1⟩,
    ⟨1608000, 194, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 1350 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk15
