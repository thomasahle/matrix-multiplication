import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk12

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨211, 163, 628⟩, ⟨211, 169, 218⟩, ⟨211, 175, 20⟩, ⟨211, 187, 212⟩,
    ⟨211, 193, 358⟩, ⟨211, 199, 222⟩, ⟨211, 205, 52⟩, ⟨211, 217, 46⟩,
    ⟨211, 223, 49⟩, ⟨211, 229, 22⟩, ⟨211, 241, 3⟩, ⟨211, 247, 3⟩,
    ⟨211, 259, 1⟩, ⟨217, 1, 1⟩, ⟨217, 7, 1⟩, ⟨217, 13, 6⟩,
    ⟨217, 19, 48⟩, ⟨217, 25, 120⟩, ⟨217, 31, 48⟩, ⟨217, 37, 6⟩,
    ⟨217, 43, 1⟩, ⟨217, 49, 1⟩, ⟨217, 55, 1⟩, ⟨217, 61, 8⟩,
    ⟨217, 67, 107⟩, ⟨217, 73, 512⟩, ⟨217, 79, 503⟩, ⟨217, 85, 110⟩,
    ⟨217, 91, 8⟩, ⟨217, 97, 1⟩, ⟨217, 103, 6⟩, ⟨217, 109, 104⟩,
    ⟨217, 115, 806⟩, ⟨217, 121, 1391⟩, ⟨217, 127, 783⟩, ⟨217, 133, 100⟩,
    ⟨217, 139, 6⟩, ⟨217, 145, 47⟩, ⟨217, 151, 478⟩, ⟨217, 157, 1365⟩,
    ⟨217, 163, 1381⟩, ⟨217, 169, 491⟩, ⟨217, 175, 46⟩, ⟨217, 181, 121⟩,
    ⟨217, 187, 489⟩, ⟨217, 193, 786⟩, ⟨217, 199, 502⟩, ⟨217, 205, 112⟩,
    ⟨217, 211, 48⟩, ⟨217, 217, 105⟩, ⟨217, 223, 108⟩, ⟨217, 229, 46⟩,
    ⟨217, 235, 6⟩, ⟨217, 241, 7⟩, ⟨217, 247, 6⟩, ⟨217, 253, 1⟩,
    ⟨217, 259, 1⟩, ⟨217, 265, 1⟩, ⟨223, 1, 1⟩, ⟨223, 7, 1⟩,
    ⟨223, 13, 6⟩, ⟨223, 19, 51⟩, ⟨223, 25, 122⟩, ⟨223, 31, 50⟩,
    ⟨223, 37, 6⟩, ⟨223, 43, 1⟩, ⟨223, 49, 1⟩, ⟨223, 55, 1⟩,
    ⟨223, 61, 8⟩, ⟨223, 67, 115⟩, ⟨223, 73, 527⟩, ⟨223, 79, 516⟩,
    ⟨223, 85, 111⟩, ⟨223, 91, 7⟩, ⟨223, 97, 1⟩, ⟨223, 103, 6⟩,
    ⟨223, 109, 108⟩, ⟨223, 115, 810⟩, ⟨223, 121, 1418⟩, ⟨223, 127, 806⟩,
    ⟨223, 133, 106⟩, ⟨223, 139, 6⟩, ⟨223, 145, 50⟩, ⟨223, 151, 499⟩,
    ⟨223, 157, 1378⟩, ⟨223, 163, 1377⟩, ⟨223, 169, 513⟩, ⟨223, 175, 46⟩,
    ⟨223, 181, 124⟩, ⟨223, 187, 496⟩, ⟨223, 193, 776⟩, ⟨223, 199, 499⟩,
    ⟨223, 205, 113⟩, ⟨223, 211, 49⟩, ⟨223, 217, 109⟩, ⟨223, 223, 111⟩,
    ⟨223, 229, 48⟩, ⟨223, 235, 6⟩, ⟨223, 241, 7⟩, ⟨223, 247, 6⟩,
    ⟨223, 253, 1⟩, ⟨223, 259, 1⟩, ⟨223, 265, 1⟩, ⟨229, 7, 1⟩,
    ⟨229, 13, 3⟩, ⟨229, 19, 23⟩, ⟨229, 25, 53⟩, ⟨229, 31, 22⟩,
    ⟨229, 37, 3⟩, ⟨229, 43, 1⟩, ⟨229, 61, 4⟩, ⟨229, 67, 49⟩,
    ⟨229, 73, 221⟩, ⟨229, 79, 230⟩, ⟨229, 85, 46⟩, ⟨229, 91, 3⟩,
    ⟨229, 103, 3⟩, ⟨229, 109, 46⟩, ⟨229, 115, 346⟩, ⟨229, 121, 631⟩,
    ⟨229, 127, 366⟩, ⟨229, 133, 46⟩, ⟨229, 145, 22⟩, ⟨229, 151, 212⟩,
    ⟨229, 157, 605⟩, ⟨229, 163, 621⟩, ⟨229, 169, 231⟩, ⟨229, 181, 53⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 1536 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk12
