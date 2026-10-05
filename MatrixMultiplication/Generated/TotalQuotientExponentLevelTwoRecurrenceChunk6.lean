import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk5
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 6; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk6

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
    ⟨72576000, 63, 2⟩,
    ⟨72576000, 68, 1⟩,
    ⟨36344000, 82, 0⟩,
    ⟨687120, 213, 2⟩,
    ⟨687120, 178, 1⟩,
    ⟨338520, 173, 0⟩,
    ⟨1372956480, 67, 2⟩,
    ⟨1372956480, 82, 1⟩,
    ⟨701934660, 67, 0⟩,
    ⟨708680, 224, 2⟩,
    ⟨708680, 170, 1⟩,
    ⟨312480, 217, 0⟩,
    ⟨30165520, 100, 2⟩,
    ⟨30165520, 41, 1⟩,
    ⟨14920080, 79, 0⟩,
    ⟨692160, 203, 2⟩,
    ⟨692160, 171, 1⟩,
    ⟨330680, 195, 0⟩,
    ⟨6824868300, 63, 2⟩,
    ⟨6824868300, 68, 1⟩,
    ⟨3473323200, 82, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨2736871728660, 82, 2⟩,
    ⟨2736871728660, 58, 1⟩,
    ⟨1476527164830, 76, 0⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨2055402540, 100, 2⟩,
    ⟨2055402540, 41, 1⟩,
    ⟨1034849115, 79, 0⟩,
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
    ⟨1729860, 63, 2⟩,
    ⟨1729860, 68, 1⟩,
    ⟨749760, 82, 0⟩,
    ⟨3368640, 213, 2⟩,
    ⟨3368640, 177, 1⟩,
    ⟨1681680, 173, 0⟩,
    ⟨2307495520, 67, 2⟩,
    ⟨2307495520, 82, 1⟩,
    ⟨1184251200, 67, 0⟩,
    ⟨2313520, 224, 2⟩,
    ⟨2313520, 170, 1⟩,
    ⟨995280, 216, 0⟩,
    ⟨1742400, 100, 2⟩,
    ⟨1742400, 41, 1⟩,
    ⟨737880, 79, 0⟩,
    ⟨1125960, 203, 2⟩,
    ⟨1125960, 170, 1⟩,
    ⟨509520, 195, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 540 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk6
