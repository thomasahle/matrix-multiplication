import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk13

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨229, 187, 207⟩, ⟨229, 193, 353⟩, ⟨229, 199, 227⟩, ⟨229, 211, 22⟩,
    ⟨229, 217, 45⟩, ⟨229, 223, 47⟩, ⟨229, 235, 3⟩, ⟨229, 241, 4⟩,
    ⟨235, 19, 3⟩, ⟨235, 25, 6⟩, ⟨235, 31, 3⟩, ⟨235, 61, 1⟩,
    ⟨235, 67, 6⟩, ⟨235, 73, 27⟩, ⟨235, 79, 26⟩, ⟨235, 85, 6⟩,
    ⟨235, 109, 6⟩, ⟨235, 115, 40⟩, ⟨235, 121, 70⟩, ⟨235, 127, 40⟩,
    ⟨235, 133, 6⟩, ⟨235, 151, 25⟩, ⟨235, 157, 70⟩, ⟨235, 163, 71⟩,
    ⟨235, 169, 26⟩, ⟨235, 175, 2⟩, ⟨235, 187, 25⟩, ⟨235, 193, 41⟩,
    ⟨235, 199, 26⟩, ⟨235, 205, 6⟩, ⟨235, 217, 6⟩, ⟨235, 223, 6⟩,
    ⟨235, 229, 3⟩, ⟨241, 13, 1⟩, ⟨241, 19, 4⟩, ⟨241, 25, 9⟩,
    ⟨241, 31, 3⟩, ⟨241, 37, 1⟩, ⟨241, 61, 1⟩, ⟨241, 67, 8⟩,
    ⟨241, 73, 35⟩, ⟨241, 79, 36⟩, ⟨241, 85, 8⟩, ⟨241, 91, 1⟩,
    ⟨241, 109, 8⟩, ⟨241, 115, 53⟩, ⟨241, 121, 95⟩, ⟨241, 127, 56⟩,
    ⟨241, 133, 7⟩, ⟨241, 139, 1⟩, ⟨241, 145, 3⟩, ⟨241, 151, 35⟩,
    ⟨241, 157, 91⟩, ⟨241, 163, 95⟩, ⟨241, 169, 35⟩, ⟨241, 175, 3⟩,
    ⟨241, 181, 9⟩, ⟨241, 187, 34⟩, ⟨241, 193, 54⟩, ⟨241, 199, 37⟩,
    ⟨241, 205, 8⟩, ⟨241, 211, 4⟩, ⟨241, 217, 7⟩, ⟨241, 223, 8⟩,
    ⟨241, 229, 4⟩, ⟨241, 241, 1⟩, ⟨241, 247, 1⟩, ⟨247, 19, 3⟩,
    ⟨247, 25, 7⟩, ⟨247, 31, 3⟩, ⟨247, 61, 1⟩, ⟨247, 67, 6⟩,
    ⟨247, 73, 27⟩, ⟨247, 79, 29⟩, ⟨247, 85, 6⟩, ⟨247, 91, 1⟩,
    ⟨247, 109, 6⟩, ⟨247, 115, 43⟩, ⟨247, 121, 73⟩, ⟨247, 127, 44⟩,
    ⟨247, 133, 6⟩, ⟨247, 145, 3⟩, ⟨247, 151, 27⟩, ⟨247, 157, 74⟩,
    ⟨247, 163, 76⟩, ⟨247, 169, 27⟩, ⟨247, 181, 7⟩, ⟨247, 187, 28⟩,
    ⟨247, 193, 44⟩, ⟨247, 199, 28⟩, ⟨247, 211, 3⟩, ⟨247, 217, 6⟩,
    ⟨247, 223, 6⟩, ⟨247, 241, 1⟩, ⟨253, 25, 1⟩, ⟨253, 67, 1⟩,
    ⟨253, 73, 4⟩, ⟨253, 79, 4⟩, ⟨253, 85, 1⟩, ⟨253, 109, 1⟩,
    ⟨253, 115, 6⟩, ⟨253, 121, 11⟩, ⟨253, 127, 6⟩, ⟨253, 133, 1⟩,
    ⟨253, 151, 4⟩, ⟨253, 157, 11⟩, ⟨253, 163, 11⟩, ⟨253, 169, 4⟩,
    ⟨253, 187, 4⟩, ⟨253, 193, 7⟩, ⟨253, 199, 4⟩, ⟨253, 205, 1⟩,
    ⟨253, 217, 1⟩, ⟨253, 223, 1⟩, ⟨253, 229, 1⟩, ⟨259, 19, 1⟩,
    ⟨259, 25, 1⟩, ⟨259, 31, 1⟩, ⟨259, 67, 1⟩, ⟨259, 73, 5⟩,
    ⟨259, 79, 5⟩, ⟨259, 85, 1⟩, ⟨259, 109, 1⟩, ⟨259, 115, 8⟩,
    ⟨259, 121, 14⟩, ⟨259, 127, 8⟩, ⟨259, 133, 1⟩, ⟨259, 145, 1⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 1664 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk13
