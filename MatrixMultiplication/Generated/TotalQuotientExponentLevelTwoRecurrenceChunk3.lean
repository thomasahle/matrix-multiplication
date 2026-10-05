import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk2
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 3; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk3

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
    ⟨1984650, 224, 2⟩,
    ⟨52563750, 170, 1⟩,
    ⟨1847100, 100, 2⟩,
    ⟨53841000, 41, 1⟩,
    ⟨2672400, 203, 2⟩,
    ⟨101944200, 170, 1⟩,
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
    ⟨4307160, 63, 2⟩,
    ⟨173412888, 68, 1⟩,
    ⟨81144, 213, 2⟩,
    ⟨1424160, 177, 1⟩,
    ⟨2167200, 67, 2⟩,
    ⟨81177120, 81, 1⟩,
    ⟨47040, 224, 2⟩,
    ⟨475104, 170, 1⟩,
    ⟨55728, 100, 2⟩,
    ⟨606960, 41, 1⟩,
    ⟨38880, 203, 2⟩,
    ⟨393120, 171, 1⟩,
    ⟨1244880, 63, 2⟩,
    ⟨41751360, 68, 1⟩,
    ⟨18348, 213, 2⟩,
    ⟨177144, 178, 1⟩,
    ⟨678468, 67, 2⟩,
    ⟨21661332, 81, 1⟩,
    ⟨19734, 224, 2⟩,
    ⟨184074, 170, 1⟩,
    ⟨31284, 100, 2⟩,
    ⟨361152, 41, 1⟩,
    ⟨21528, 203, 2⟩,
    ⟨210600, 171, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨65688480, 68, 1⟩,
    ⟨29292648, 177, 1⟩,
    ⟨417875436, 81, 1⟩,
    ⟨464500608, 170, 1⟩,
    ⟨4576704, 41, 1⟩,
    ⟨52968960, 170, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 1⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 270 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk3
