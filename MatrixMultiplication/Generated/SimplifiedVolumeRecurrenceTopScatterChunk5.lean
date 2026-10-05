import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk5

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨79, 1, 3⟩, ⟨79, 7, 5⟩, ⟨79, 13, 27⟩, ⟨79, 19, 222⟩,
    ⟨79, 25, 536⟩, ⟨79, 31, 226⟩, ⟨79, 37, 26⟩, ⟨79, 43, 5⟩,
    ⟨79, 49, 3⟩, ⟨79, 55, 4⟩, ⟨79, 61, 34⟩, ⟨79, 67, 495⟩,
    ⟨79, 73, 2216⟩, ⟨79, 79, 2259⟩, ⟨79, 85, 486⟩, ⟨79, 91, 33⟩,
    ⟨79, 97, 5⟩, ⟨79, 103, 26⟩, ⟨79, 109, 471⟩, ⟨79, 115, 3429⟩,
    ⟨79, 121, 6142⟩, ⟨79, 127, 3461⟩, ⟨79, 133, 490⟩, ⟨79, 139, 26⟩,
    ⟨79, 145, 226⟩, ⟨79, 151, 2151⟩, ⟨79, 157, 6259⟩, ⟨79, 163, 6471⟩,
    ⟨79, 169, 2335⟩, ⟨79, 175, 215⟩, ⟨79, 181, 568⟩, ⟨79, 187, 2347⟩,
    ⟨79, 193, 3939⟩, ⟨79, 199, 2466⟩, ⟨79, 205, 557⟩, ⟨79, 211, 222⟩,
    ⟨79, 217, 491⟩, ⟨79, 223, 536⟩, ⟨79, 229, 228⟩, ⟨79, 235, 27⟩,
    ⟨79, 241, 36⟩, ⟨79, 247, 28⟩, ⟨79, 253, 4⟩, ⟨79, 259, 5⟩,
    ⟨79, 265, 3⟩, ⟨85, 1, 1⟩, ⟨85, 7, 1⟩, ⟨85, 13, 6⟩,
    ⟨85, 19, 47⟩, ⟨85, 25, 115⟩, ⟨85, 31, 45⟩, ⟨85, 37, 6⟩,
    ⟨85, 43, 1⟩, ⟨85, 49, 1⟩, ⟨85, 55, 1⟩, ⟨85, 61, 8⟩,
    ⟨85, 67, 104⟩, ⟨85, 73, 470⟩, ⟨85, 79, 469⟩, ⟨85, 85, 100⟩,
    ⟨85, 91, 7⟩, ⟨85, 97, 1⟩, ⟨85, 103, 5⟩, ⟨85, 109, 102⟩,
    ⟨85, 115, 727⟩, ⟨85, 121, 1243⟩, ⟨85, 127, 737⟩, ⟨85, 133, 99⟩,
    ⟨85, 139, 6⟩, ⟨85, 145, 47⟩, ⟨85, 151, 442⟩, ⟨85, 157, 1221⟩,
    ⟨85, 163, 1286⟩, ⟨85, 169, 478⟩, ⟨85, 175, 46⟩, ⟨85, 181, 119⟩,
    ⟨85, 187, 471⟩, ⟨85, 193, 781⟩, ⟨85, 199, 492⟩, ⟨85, 205, 118⟩,
    ⟨85, 211, 48⟩, ⟨85, 217, 106⟩, ⟨85, 223, 106⟩, ⟨85, 229, 46⟩,
    ⟨85, 235, 6⟩, ⟨85, 241, 8⟩, ⟨85, 247, 6⟩, ⟨85, 253, 1⟩,
    ⟨85, 259, 1⟩, ⟨85, 265, 1⟩, ⟨91, 19, 3⟩, ⟨91, 25, 8⟩,
    ⟨91, 31, 3⟩, ⟨91, 61, 1⟩, ⟨91, 67, 7⟩, ⟨91, 73, 33⟩,
    ⟨91, 79, 34⟩, ⟨91, 85, 7⟩, ⟨91, 91, 1⟩, ⟨91, 109, 7⟩,
    ⟨91, 115, 49⟩, ⟨91, 121, 84⟩, ⟨91, 127, 52⟩, ⟨91, 133, 7⟩,
    ⟨91, 145, 3⟩, ⟨91, 151, 32⟩, ⟨91, 157, 86⟩, ⟨91, 163, 89⟩,
    ⟨91, 169, 34⟩, ⟨91, 175, 3⟩, ⟨91, 181, 8⟩, ⟨91, 187, 32⟩,
    ⟨91, 193, 51⟩, ⟨91, 199, 33⟩, ⟨91, 205, 8⟩, ⟨91, 211, 3⟩,
    ⟨91, 217, 7⟩, ⟨91, 223, 8⟩, ⟨91, 229, 3⟩, ⟨91, 241, 1⟩,
    ⟨97, 19, 1⟩, ⟨97, 25, 1⟩, ⟨97, 31, 1⟩, ⟨97, 67, 1⟩,
    ⟨97, 73, 5⟩, ⟨97, 79, 5⟩, ⟨97, 85, 1⟩, ⟨97, 109, 1⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 640 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk5
