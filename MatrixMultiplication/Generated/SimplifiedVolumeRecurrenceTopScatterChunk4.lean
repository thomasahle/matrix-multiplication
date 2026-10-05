import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk4

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨55, 199, 4⟩, ⟨55, 205, 1⟩, ⟨55, 217, 1⟩, ⟨55, 223, 1⟩,
    ⟨55, 229, 1⟩, ⟨61, 13, 1⟩, ⟨61, 19, 4⟩, ⟨61, 25, 9⟩,
    ⟨61, 31, 4⟩, ⟨61, 61, 1⟩, ⟨61, 67, 8⟩, ⟨61, 73, 35⟩,
    ⟨61, 79, 35⟩, ⟨61, 85, 7⟩, ⟨61, 91, 1⟩, ⟨61, 109, 8⟩,
    ⟨61, 115, 55⟩, ⟨61, 121, 93⟩, ⟨61, 127, 54⟩, ⟨61, 133, 8⟩,
    ⟨61, 145, 4⟩, ⟨61, 151, 36⟩, ⟨61, 157, 93⟩, ⟨61, 163, 93⟩,
    ⟨61, 169, 34⟩, ⟨61, 175, 3⟩, ⟨61, 181, 9⟩, ⟨61, 187, 36⟩,
    ⟨61, 193, 57⟩, ⟨61, 199, 35⟩, ⟨61, 205, 8⟩, ⟨61, 211, 4⟩,
    ⟨61, 217, 8⟩, ⟨61, 223, 8⟩, ⟨61, 229, 3⟩, ⟨61, 235, 1⟩,
    ⟨61, 241, 1⟩, ⟨61, 247, 1⟩, ⟨67, 1, 1⟩, ⟨67, 7, 1⟩,
    ⟨67, 13, 6⟩, ⟨67, 19, 49⟩, ⟨67, 25, 120⟩, ⟨67, 31, 45⟩,
    ⟨67, 37, 6⟩, ⟨67, 43, 1⟩, ⟨67, 49, 1⟩, ⟨67, 55, 1⟩,
    ⟨67, 61, 8⟩, ⟨67, 67, 107⟩, ⟨67, 73, 496⟩, ⟨67, 79, 493⟩,
    ⟨67, 85, 101⟩, ⟨67, 91, 7⟩, ⟨67, 97, 1⟩, ⟨67, 103, 6⟩,
    ⟨67, 109, 106⟩, ⟨67, 115, 772⟩, ⟨67, 121, 1296⟩, ⟨67, 127, 737⟩,
    ⟨67, 133, 104⟩, ⟨67, 139, 6⟩, ⟨67, 145, 49⟩, ⟨67, 151, 483⟩,
    ⟨67, 157, 1321⟩, ⟨67, 163, 1316⟩, ⟨67, 169, 467⟩, ⟨67, 175, 45⟩,
    ⟨67, 181, 122⟩, ⟨67, 187, 489⟩, ⟨67, 193, 800⟩, ⟨67, 199, 492⟩,
    ⟨67, 205, 112⟩, ⟨67, 211, 50⟩, ⟨67, 217, 107⟩, ⟨67, 223, 110⟩,
    ⟨67, 229, 48⟩, ⟨67, 235, 6⟩, ⟨67, 241, 8⟩, ⟨67, 247, 6⟩,
    ⟨67, 253, 1⟩, ⟨67, 259, 1⟩, ⟨67, 265, 1⟩, ⟨73, 1, 3⟩,
    ⟨73, 7, 5⟩, ⟨73, 13, 27⟩, ⟨73, 19, 225⟩, ⟨73, 25, 549⟩,
    ⟨73, 31, 220⟩, ⟨73, 37, 25⟩, ⟨73, 43, 5⟩, ⟨73, 49, 3⟩,
    ⟨73, 55, 4⟩, ⟨73, 61, 35⟩, ⟨73, 67, 490⟩, ⟨73, 73, 2226⟩,
    ⟨73, 79, 2265⟩, ⟨73, 85, 468⟩, ⟨73, 91, 32⟩, ⟨73, 97, 5⟩,
    ⟨73, 103, 25⟩, ⟨73, 109, 477⟩, ⟨73, 115, 3584⟩, ⟨73, 121, 5913⟩,
    ⟨73, 127, 3400⟩, ⟨73, 133, 463⟩, ⟨73, 139, 25⟩, ⟨73, 145, 233⟩,
    ⟨73, 151, 2196⟩, ⟨73, 157, 6331⟩, ⟨73, 163, 6306⟩, ⟨73, 169, 2227⟩,
    ⟨73, 175, 213⟩, ⟨73, 181, 570⟩, ⟨73, 187, 2457⟩, ⟨73, 193, 3761⟩,
    ⟨73, 199, 2372⟩, ⟨73, 205, 522⟩, ⟨73, 211, 231⟩, ⟨73, 217, 528⟩,
    ⟨73, 223, 507⟩, ⟨73, 229, 230⟩, ⟨73, 235, 25⟩, ⟨73, 241, 35⟩,
    ⟨73, 247, 28⟩, ⟨73, 253, 4⟩, ⟨73, 259, 5⟩, ⟨73, 265, 3⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 512 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk4
