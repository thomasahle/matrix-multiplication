import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk6

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨97, 115, 8⟩, ⟨97, 121, 14⟩, ⟨97, 127, 8⟩, ⟨97, 133, 1⟩,
    ⟨97, 145, 1⟩, ⟨97, 151, 5⟩, ⟨97, 157, 13⟩, ⟨97, 163, 14⟩,
    ⟨97, 169, 5⟩, ⟨97, 181, 1⟩, ⟨97, 187, 5⟩, ⟨97, 193, 8⟩,
    ⟨97, 199, 5⟩, ⟨97, 211, 1⟩, ⟨97, 217, 1⟩, ⟨97, 223, 1⟩,
    ⟨103, 19, 3⟩, ⟨103, 25, 6⟩, ⟨103, 31, 3⟩, ⟨103, 61, 1⟩,
    ⟨103, 67, 6⟩, ⟨103, 73, 25⟩, ⟨103, 79, 26⟩, ⟨103, 85, 5⟩,
    ⟨103, 109, 6⟩, ⟨103, 115, 39⟩, ⟨103, 121, 66⟩, ⟨103, 127, 38⟩,
    ⟨103, 133, 5⟩, ⟨103, 151, 25⟩, ⟨103, 157, 71⟩, ⟨103, 163, 69⟩,
    ⟨103, 169, 26⟩, ⟨103, 175, 3⟩, ⟨103, 187, 26⟩, ⟨103, 193, 39⟩,
    ⟨103, 199, 26⟩, ⟨103, 205, 6⟩, ⟨103, 217, 6⟩, ⟨103, 223, 6⟩,
    ⟨103, 229, 3⟩, ⟨103, 241, 1⟩, ⟨109, 1, 1⟩, ⟨109, 7, 1⟩,
    ⟨109, 13, 6⟩, ⟨109, 19, 47⟩, ⟨109, 25, 117⟩, ⟨109, 31, 47⟩,
    ⟨109, 37, 6⟩, ⟨109, 43, 1⟩, ⟨109, 49, 1⟩, ⟨109, 55, 1⟩,
    ⟨109, 61, 7⟩, ⟨109, 67, 105⟩, ⟨109, 73, 470⟩, ⟨109, 79, 464⟩,
    ⟨109, 85, 101⟩, ⟨109, 91, 7⟩, ⟨109, 97, 1⟩, ⟨109, 103, 6⟩,
    ⟨109, 109, 103⟩, ⟨109, 115, 736⟩, ⟨109, 121, 1284⟩, ⟨109, 127, 734⟩,
    ⟨109, 133, 98⟩, ⟨109, 139, 6⟩, ⟨109, 145, 48⟩, ⟨109, 151, 483⟩,
    ⟨109, 157, 1292⟩, ⟨109, 163, 1234⟩, ⟨109, 169, 464⟩, ⟨109, 175, 46⟩,
    ⟨109, 181, 124⟩, ⟨109, 187, 496⟩, ⟨109, 193, 792⟩, ⟨109, 199, 458⟩,
    ⟨109, 205, 106⟩, ⟨109, 211, 49⟩, ⟨109, 217, 105⟩, ⟨109, 223, 101⟩,
    ⟨109, 229, 46⟩, ⟨109, 235, 5⟩, ⟨109, 241, 8⟩, ⟨109, 247, 6⟩,
    ⟨109, 253, 1⟩, ⟨109, 259, 1⟩, ⟨109, 265, 1⟩, ⟨115, 1, 5⟩,
    ⟨115, 7, 7⟩, ⟨115, 13, 41⟩, ⟨115, 19, 343⟩, ⟨115, 25, 824⟩,
    ⟨115, 31, 342⟩, ⟨115, 37, 40⟩, ⟨115, 43, 7⟩, ⟨115, 49, 5⟩,
    ⟨115, 55, 7⟩, ⟨115, 61, 56⟩, ⟨115, 67, 742⟩, ⟨115, 73, 3477⟩,
    ⟨115, 79, 3403⟩, ⟨115, 85, 712⟩, ⟨115, 91, 50⟩, ⟨115, 97, 8⟩,
    ⟨115, 103, 40⟩, ⟨115, 109, 748⟩, ⟨115, 115, 5280⟩, ⟨115, 121, 8987⟩,
    ⟨115, 127, 5096⟩, ⟨115, 133, 707⟩, ⟨115, 139, 40⟩, ⟨115, 145, 346⟩,
    ⟨115, 151, 3426⟩, ⟨115, 157, 9456⟩, ⟨115, 163, 8897⟩, ⟨115, 169, 3231⟩,
    ⟨115, 175, 316⟩, ⟨115, 181, 898⟩, ⟨115, 187, 3728⟩, ⟨115, 193, 5849⟩,
    ⟨115, 199, 3590⟩, ⟨115, 205, 797⟩, ⟨115, 211, 355⟩, ⟨115, 217, 762⟩,
    ⟨115, 223, 808⟩, ⟨115, 229, 340⟩, ⟨115, 235, 39⟩, ⟨115, 241, 54⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 768 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk6
