import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk3

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨25, 211, 54⟩, ⟨25, 217, 120⟩, ⟨25, 223, 115⟩, ⟨25, 229, 52⟩,
    ⟨25, 235, 6⟩, ⟨25, 241, 9⟩, ⟨25, 247, 7⟩, ⟨25, 253, 1⟩,
    ⟨25, 259, 1⟩, ⟨25, 265, 1⟩, ⟨31, 55, 1⟩, ⟨31, 61, 3⟩,
    ⟨31, 67, 47⟩, ⟨31, 73, 218⟩, ⟨31, 79, 216⟩, ⟨31, 85, 48⟩,
    ⟨31, 91, 3⟩, ⟨31, 97, 1⟩, ⟨31, 103, 3⟩, ⟨31, 109, 45⟩,
    ⟨31, 115, 332⟩, ⟨31, 121, 607⟩, ⟨31, 127, 352⟩, ⟨31, 133, 46⟩,
    ⟨31, 139, 3⟩, ⟨31, 145, 22⟩, ⟨31, 151, 213⟩, ⟨31, 157, 590⟩,
    ⟨31, 163, 602⟩, ⟨31, 169, 221⟩, ⟨31, 175, 20⟩, ⟨31, 181, 54⟩,
    ⟨31, 187, 224⟩, ⟨31, 193, 340⟩, ⟨31, 199, 229⟩, ⟨31, 205, 51⟩,
    ⟨31, 211, 23⟩, ⟨31, 217, 47⟩, ⟨31, 223, 49⟩, ⟨31, 229, 21⟩,
    ⟨31, 235, 3⟩, ⟨31, 241, 3⟩, ⟨31, 247, 3⟩, ⟨31, 259, 1⟩,
    ⟨37, 67, 6⟩, ⟨37, 73, 27⟩, ⟨37, 79, 26⟩, ⟨37, 85, 6⟩,
    ⟨37, 109, 6⟩, ⟨37, 115, 40⟩, ⟨37, 121, 68⟩, ⟨37, 127, 41⟩,
    ⟨37, 133, 6⟩, ⟨37, 145, 3⟩, ⟨37, 151, 26⟩, ⟨37, 157, 68⟩,
    ⟨37, 163, 70⟩, ⟨37, 169, 27⟩, ⟨37, 175, 3⟩, ⟨37, 181, 6⟩,
    ⟨37, 187, 26⟩, ⟨37, 193, 41⟩, ⟨37, 199, 27⟩, ⟨37, 205, 6⟩,
    ⟨37, 211, 3⟩, ⟨37, 217, 6⟩, ⟨37, 223, 6⟩, ⟨37, 229, 3⟩,
    ⟨37, 241, 1⟩, ⟨43, 67, 1⟩, ⟨43, 73, 5⟩, ⟨43, 79, 5⟩,
    ⟨43, 85, 1⟩, ⟨43, 109, 1⟩, ⟨43, 115, 7⟩, ⟨43, 121, 12⟩,
    ⟨43, 127, 7⟩, ⟨43, 133, 1⟩, ⟨43, 145, 1⟩, ⟨43, 151, 5⟩,
    ⟨43, 157, 13⟩, ⟨43, 163, 13⟩, ⟨43, 169, 5⟩, ⟨43, 175, 1⟩,
    ⟨43, 181, 1⟩, ⟨43, 187, 5⟩, ⟨43, 193, 8⟩, ⟨43, 199, 5⟩,
    ⟨43, 205, 1⟩, ⟨43, 211, 1⟩, ⟨43, 217, 1⟩, ⟨43, 223, 1⟩,
    ⟨43, 229, 1⟩, ⟨49, 67, 1⟩, ⟨49, 73, 3⟩, ⟨49, 79, 3⟩,
    ⟨49, 85, 1⟩, ⟨49, 109, 1⟩, ⟨49, 115, 5⟩, ⟨49, 121, 9⟩,
    ⟨49, 127, 5⟩, ⟨49, 133, 1⟩, ⟨49, 151, 3⟩, ⟨49, 157, 9⟩,
    ⟨49, 163, 9⟩, ⟨49, 169, 3⟩, ⟨49, 181, 1⟩, ⟨49, 187, 3⟩,
    ⟨49, 193, 5⟩, ⟨49, 199, 3⟩, ⟨49, 217, 1⟩, ⟨49, 223, 1⟩,
    ⟨55, 25, 1⟩, ⟨55, 67, 1⟩, ⟨55, 73, 4⟩, ⟨55, 79, 4⟩,
    ⟨55, 85, 1⟩, ⟨55, 109, 1⟩, ⟨55, 115, 7⟩, ⟨55, 121, 11⟩,
    ⟨55, 127, 7⟩, ⟨55, 133, 1⟩, ⟨55, 151, 4⟩, ⟨55, 157, 11⟩,
    ⟨55, 163, 11⟩, ⟨55, 169, 4⟩, ⟨55, 187, 4⟩, ⟨55, 193, 7⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 384 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk3
