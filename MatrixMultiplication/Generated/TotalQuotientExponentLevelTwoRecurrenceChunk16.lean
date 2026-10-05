import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk15
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 16; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk16

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
    ⟨1472064, 63, 2⟩,
    ⟨43793904, 82, 0⟩,
    ⟨59856, 213, 2⟩,
    ⟨909672, 173, 0⟩,
    ⟨2725512, 67, 2⟩,
    ⟨82969656, 67, 0⟩,
    ⟨32160, 224, 2⟩,
    ⟨323280, 217, 0⟩,
    ⟨32868, 100, 2⟩,
    ⟨358116, 79, 0⟩,
    ⟨34980, 203, 2⟩,
    ⟨355608, 195, 0⟩,
    ⟨274159872, 63, 2⟩,
    ⟨11180582280, 82, 0⟩,
    ⟨5583312, 213, 2⟩,
    ⟨125768916, 171, 0⟩,
    ⟨5650215480, 67, 2⟩,
    ⟨247479438024, 70, 0⟩,
    ⟨2767590, 224, 2⟩,
    ⟨63365778, 215, 0⟩,
    ⟨2960118, 100, 2⟩,
    ⟨65170728, 78, 0⟩,
    ⟨2839788, 203, 2⟩,
    ⟨62571600, 193, 0⟩,
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
    ⟨66456, 63, 2⟩,
    ⟨835224, 82, 0⟩,
    ⟨70200, 213, 2⟩,
    ⟨839280, 173, 0⟩,
    ⟨90720, 67, 2⟩,
    ⟨1170720, 67, 0⟩,
    ⟨62040, 224, 2⟩,
    ⟨708576, 217, 0⟩,
    ⟨6334416, 100, 2⟩,
    ⟨258559344, 78, 0⟩,
    ⟨135072, 203, 2⟩,
    ⟨2589552, 194, 0⟩,
    ⟨881760, 63, 2⟩,
    ⟨28943772, 82, 0⟩,
    ⟨17760, 213, 2⟩,
    ⟨164220, 173, 0⟩,
    ⟨1076988, 67, 2⟩,
    ⟨34516152, 67, 0⟩,
    ⟨24738, 224, 2⟩,
    ⟨305748, 217, 0⟩,
    ⟨18414, 100, 2⟩,
    ⟨180180, 79, 0⟩,
    ⟨31320, 203, 2⟩,
    ⟨469620, 194, 0⟩,
    ⟨46656, 68, 1⟩,
    ⟨508032, 82, 0⟩,
    ⟨90720, 178, 1⟩,
    ⟨1670544, 173, 0⟩,
    ⟨3915336, 82, 1⟩,
    ⟨124526784, 66, 0⟩,
    ⟨42168, 171, 1⟩,
    ⟨442008, 217, 0⟩,
    ⟨47736, 41, 1⟩,
    ⟨519996, 79, 0⟩,
    ⟨42624, 171, 1⟩,
    ⟨506304, 195, 0⟩,
    ⟨754689000, 68, 1⟩,
    ⟨33005065600, 82, 0⟩,
    ⟨5753000, 177, 1⟩,
    ⟨135038600, 171, 0⟩,
    ⟨5657814000, 82, 1⟩,
    ⟨249886785000, 70, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 1440 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk16
