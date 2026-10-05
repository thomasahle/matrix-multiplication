import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk10

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨175, 43, 1⟩, ⟨175, 61, 3⟩, ⟨175, 67, 47⟩, ⟨175, 73, 205⟩,
    ⟨175, 79, 217⟩, ⟨175, 85, 46⟩, ⟨175, 91, 3⟩, ⟨175, 103, 2⟩,
    ⟨175, 109, 45⟩, ⟨175, 115, 320⟩, ⟨175, 121, 553⟩, ⟨175, 127, 337⟩,
    ⟨175, 133, 45⟩, ⟨175, 145, 21⟩, ⟨175, 151, 206⟩, ⟨175, 157, 554⟩,
    ⟨175, 163, 570⟩, ⟨175, 169, 207⟩, ⟨175, 181, 54⟩, ⟨175, 187, 204⟩,
    ⟨175, 193, 344⟩, ⟨175, 199, 213⟩, ⟨175, 211, 20⟩, ⟨175, 217, 45⟩,
    ⟨175, 223, 47⟩, ⟨175, 235, 2⟩, ⟨175, 241, 3⟩, ⟨181, 7, 1⟩,
    ⟨181, 13, 7⟩, ⟨181, 19, 57⟩, ⟨181, 25, 138⟩, ⟨181, 31, 55⟩,
    ⟨181, 37, 6⟩, ⟨181, 43, 1⟩, ⟨181, 49, 1⟩, ⟨181, 61, 9⟩,
    ⟨181, 67, 121⟩, ⟨181, 73, 570⟩, ⟨181, 79, 564⟩, ⟨181, 85, 116⟩,
    ⟨181, 91, 8⟩, ⟨181, 97, 1⟩, ⟨181, 109, 121⟩, ⟨181, 115, 876⟩,
    ⟨181, 121, 1549⟩, ⟨181, 127, 857⟩, ⟨181, 133, 110⟩, ⟨181, 139, 7⟩,
    ⟨181, 151, 576⟩, ⟨181, 157, 1483⟩, ⟨181, 163, 1517⟩, ⟨181, 169, 530⟩,
    ⟨181, 175, 52⟩, ⟨181, 187, 534⟩, ⟨181, 193, 881⟩, ⟨181, 199, 535⟩,
    ⟨181, 205, 124⟩, ⟨181, 217, 121⟩, ⟨181, 223, 122⟩, ⟨181, 229, 53⟩,
    ⟨181, 241, 9⟩, ⟨181, 247, 7⟩, ⟨181, 259, 1⟩, ⟨187, 1, 3⟩,
    ⟨187, 7, 5⟩, ⟨187, 13, 28⟩, ⟨187, 19, 224⟩, ⟨187, 25, 566⟩,
    ⟨187, 31, 221⟩, ⟨187, 37, 26⟩, ⟨187, 43, 5⟩, ⟨187, 49, 3⟩,
    ⟨187, 55, 4⟩, ⟨187, 61, 36⟩, ⟨187, 67, 506⟩, ⟨187, 73, 2387⟩,
    ⟨187, 79, 2437⟩, ⟨187, 85, 475⟩, ⟨187, 91, 32⟩, ⟨187, 97, 5⟩,
    ⟨187, 103, 25⟩, ⟨187, 109, 485⟩, ⟨187, 115, 3631⟩, ⟨187, 121, 6452⟩,
    ⟨187, 127, 3573⟩, ⟨187, 133, 470⟩, ⟨187, 139, 26⟩, ⟨187, 145, 213⟩,
    ⟨187, 151, 2278⟩, ⟨187, 157, 6354⟩, ⟨187, 163, 5956⟩, ⟨187, 169, 2089⟩,
    ⟨187, 175, 209⟩, ⟨187, 181, 544⟩, ⟨187, 187, 2238⟩, ⟨187, 193, 3596⟩,
    ⟨187, 199, 2243⟩, ⟨187, 205, 524⟩, ⟨187, 211, 220⟩, ⟨187, 217, 491⟩,
    ⟨187, 223, 494⟩, ⟨187, 229, 218⟩, ⟨187, 235, 26⟩, ⟨187, 241, 34⟩,
    ⟨187, 247, 27⟩, ⟨187, 253, 4⟩, ⟨187, 259, 5⟩, ⟨187, 265, 3⟩,
    ⟨193, 1, 5⟩, ⟨193, 7, 7⟩, ⟨193, 13, 42⟩, ⟨193, 19, 359⟩,
    ⟨193, 25, 890⟩, ⟨193, 31, 350⟩, ⟨193, 37, 41⟩, ⟨193, 43, 7⟩,
    ⟨193, 49, 5⟩, ⟨193, 55, 7⟩, ⟨193, 61, 55⟩, ⟨193, 67, 803⟩,
    ⟨193, 73, 4016⟩, ⟨193, 79, 3894⟩, ⟨193, 85, 778⟩, ⟨193, 91, 54⟩,
    ⟨193, 97, 8⟩, ⟨193, 103, 40⟩, ⟨193, 109, 770⟩, ⟨193, 115, 5596⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 1280 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk10
