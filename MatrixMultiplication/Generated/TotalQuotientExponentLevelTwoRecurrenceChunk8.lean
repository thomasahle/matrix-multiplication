import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk7
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 8; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk8

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
    ⟨164428704, 63, 2⟩,
    ⟨2396704464, 68, 1⟩,
    ⟨157143888, 82, 0⟩,
    ⟨72732, 213, 2⟩,
    ⟨559416, 178, 1⟩,
    ⟨74844, 174, 0⟩,
    ⟨127776, 67, 2⟩,
    ⟨1143120, 82, 1⟩,
    ⟨136752, 67, 0⟩,
    ⟨219648, 224, 2⟩,
    ⟨2426688, 170, 1⟩,
    ⟨223344, 217, 0⟩,
    ⟨6813840, 100, 2⟩,
    ⟨88273680, 41, 1⟩,
    ⟨5971680, 79, 0⟩,
    ⟨145464, 203, 2⟩,
    ⟨1123584, 170, 1⟩,
    ⟨149688, 195, 0⟩,
    ⟨49224, 63, 2⟩,
    ⟨337008, 68, 1⟩,
    ⟨51072, 82, 0⟩,
    ⟨50232, 213, 2⟩,
    ⟨339864, 178, 1⟩,
    ⟨51492, 174, 0⟩,
    ⟨51176664, 67, 2⟩,
    ⟨769991376, 82, 1⟩,
    ⟨52681860, 66, 0⟩,
    ⟨52752, 224, 2⟩,
    ⟨344400, 170, 1⟩,
    ⟨53088, 217, 0⟩,
    ⟨1607172, 100, 2⟩,
    ⟨20559336, 41, 1⟩,
    ⟨1353408, 79, 0⟩,
    ⟨50232, 203, 2⟩,
    ⟨340536, 171, 1⟩,
    ⟨51408, 195, 0⟩,
    ⟨53629632, 68, 1⟩,
    ⟨1670832, 82, 0⟩,
    ⟨327840, 178, 1⟩,
    ⟨33720, 174, 0⟩,
    ⟨544884, 82, 1⟩,
    ⟨45696, 67, 0⟩,
    ⟨335280, 170, 1⟩,
    ⟨34560, 218, 0⟩,
    ⟨73802592, 41, 1⟩,
    ⟨2595504, 79, 0⟩,
    ⟨329640, 171, 1⟩,
    ⟨33240, 195, 0⟩,
    ⟨17689646720, 68, 1⟩,
    ⟨203485200, 82, 0⟩,
    ⟨48139832, 177, 1⟩,
    ⟨1906528, 173, 0⟩,
    ⟨168120645488, 78, 1⟩,
    ⟨1441408496, 66, 0⟩,
    ⟨48964772, 170, 1⟩,
    ⟨2034852, 216, 0⟩,
    ⟨7123668544, 41, 1⟩,
    ⟨92869912, 79, 0⟩,
    ⟨48249824, 170, 1⟩,
    ⟨1906528, 194, 0⟩,
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
    ⟨137305152, 68, 1⟩,
    ⟨3648960, 82, 0⟩,
    ⟨524928, 178, 1⟩,
    ⟨50496, 174, 0⟩,
    ⟨905184, 82, 1⟩,
    ⟨74256, 67, 0⟩
  ]

opaque inputs_eq :
    edgeInputRangeWithMassThree MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 720 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk8
