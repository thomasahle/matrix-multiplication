import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk2

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨1, 73, 3⟩, ⟨1, 79, 3⟩, ⟨1, 85, 1⟩, ⟨1, 109, 1⟩,
    ⟨1, 115, 5⟩, ⟨1, 121, 9⟩, ⟨1, 127, 5⟩, ⟨1, 133, 1⟩,
    ⟨1, 151, 3⟩, ⟨1, 157, 8⟩, ⟨1, 163, 9⟩, ⟨1, 169, 3⟩,
    ⟨1, 187, 3⟩, ⟨1, 193, 5⟩, ⟨1, 199, 3⟩, ⟨1, 205, 1⟩,
    ⟨1, 217, 1⟩, ⟨1, 223, 1⟩, ⟨7, 67, 1⟩, ⟨7, 73, 5⟩,
    ⟨7, 79, 5⟩, ⟨7, 85, 1⟩, ⟨7, 109, 1⟩, ⟨7, 115, 7⟩,
    ⟨7, 121, 12⟩, ⟨7, 127, 7⟩, ⟨7, 133, 1⟩, ⟨7, 145, 1⟩,
    ⟨7, 151, 5⟩, ⟨7, 157, 13⟩, ⟨7, 163, 12⟩, ⟨7, 169, 4⟩,
    ⟨7, 175, 1⟩, ⟨7, 181, 1⟩, ⟨7, 187, 5⟩, ⟨7, 193, 7⟩,
    ⟨7, 199, 5⟩, ⟨7, 205, 1⟩, ⟨7, 211, 1⟩, ⟨7, 217, 1⟩,
    ⟨7, 223, 1⟩, ⟨7, 229, 1⟩, ⟨13, 61, 1⟩, ⟨13, 67, 6⟩,
    ⟨13, 73, 26⟩, ⟨13, 79, 27⟩, ⟨13, 85, 5⟩, ⟨13, 109, 6⟩,
    ⟨13, 115, 42⟩, ⟨13, 121, 70⟩, ⟨13, 127, 40⟩, ⟨13, 133, 6⟩,
    ⟨13, 145, 3⟩, ⟨13, 151, 27⟩, ⟨13, 157, 70⟩, ⟨13, 163, 71⟩,
    ⟨13, 169, 26⟩, ⟨13, 175, 3⟩, ⟨13, 181, 7⟩, ⟨13, 187, 26⟩,
    ⟨13, 193, 43⟩, ⟨13, 199, 27⟩, ⟨13, 205, 6⟩, ⟨13, 211, 3⟩,
    ⟨13, 217, 6⟩, ⟨13, 223, 6⟩, ⟨13, 229, 3⟩, ⟨13, 241, 1⟩,
    ⟨19, 55, 1⟩, ⟨19, 61, 4⟩, ⟨19, 67, 49⟩, ⟨19, 73, 218⟩,
    ⟨19, 79, 224⟩, ⟨19, 85, 47⟩, ⟨19, 91, 3⟩, ⟨19, 97, 1⟩,
    ⟨19, 103, 3⟩, ⟨19, 109, 48⟩, ⟨19, 115, 344⟩, ⟨19, 121, 596⟩,
    ⟨19, 127, 348⟩, ⟨19, 133, 45⟩, ⟨19, 139, 3⟩, ⟨19, 145, 22⟩,
    ⟨19, 151, 217⟩, ⟨19, 157, 590⟩, ⟨19, 163, 625⟩, ⟨19, 169, 222⟩,
    ⟨19, 175, 21⟩, ⟨19, 181, 56⟩, ⟨19, 187, 224⟩, ⟨19, 193, 361⟩,
    ⟨19, 199, 234⟩, ⟨19, 205, 54⟩, ⟨19, 211, 23⟩, ⟨19, 217, 48⟩,
    ⟨19, 223, 49⟩, ⟨19, 229, 23⟩, ⟨19, 235, 3⟩, ⟨19, 241, 4⟩,
    ⟨19, 247, 3⟩, ⟨19, 259, 1⟩, ⟨25, 55, 1⟩, ⟨25, 61, 8⟩,
    ⟨25, 67, 117⟩, ⟨25, 73, 512⟩, ⟨25, 79, 544⟩, ⟨25, 85, 115⟩,
    ⟨25, 91, 8⟩, ⟨25, 97, 1⟩, ⟨25, 103, 6⟩, ⟨25, 109, 113⟩,
    ⟨25, 115, 834⟩, ⟨25, 121, 1489⟩, ⟨25, 127, 835⟩, ⟨25, 133, 113⟩,
    ⟨25, 139, 6⟩, ⟨25, 145, 52⟩, ⟨25, 151, 548⟩, ⟨25, 157, 1484⟩,
    ⟨25, 163, 1447⟩, ⟨25, 169, 528⟩, ⟨25, 175, 51⟩, ⟨25, 181, 132⟩,
    ⟨25, 187, 559⟩, ⟨25, 193, 894⟩, ⟨25, 199, 559⟩, ⟨25, 205, 129⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 256 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk2
