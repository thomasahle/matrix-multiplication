import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk11
import MatrixMultiplication.SimplifiedExponentRecurrence

/-! Exact level-two retained-rate recurrence chunk 12; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk12

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
    ⟨1115392824, 63, 2⟩,
    ⟨2263795716, 68, 1⟩,
    ⟨2263795716, 82, 0⟩,
    ⟨256632, 213, 2⟩,
    ⟨564768, 177, 1⟩,
    ⟨564768, 173, 0⟩,
    ⟨745920, 67, 2⟩,
    ⟨1757574, 82, 1⟩,
    ⟨1757574, 67, 0⟩,
    ⟨507048, 224, 2⟩,
    ⟨1132644, 170, 1⟩,
    ⟨1132644, 216, 0⟩,
    ⟨46339392, 100, 2⟩,
    ⟨104634816, 41, 1⟩,
    ⟨104634816, 79, 0⟩,
    ⟨258408, 203, 2⟩,
    ⟨562770, 170, 1⟩,
    ⟨562770, 194, 0⟩,
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
    ⟨301943024, 68, 1⟩,
    ⟨46808142, 82, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 0⟩,
    ⟨301507194, 82, 1⟩,
    ⟨46982474, 66, 0⟩,
    ⟨295841404, 170, 1⟩,
    ⟨52996928, 215, 0⟩,
    ⟨1205170539564, 38, 1⟩,
    ⟨218343508056, 78, 0⟩,
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
    edgeInputRangeWithMassThree MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 1080 90 =
      expectedInputs := by
  unfold expectedInputs
  unfold MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables pos3AChunks pos3AlphaChunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk12
