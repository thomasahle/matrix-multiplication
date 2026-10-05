import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk11

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨193, 121, 10651⟩, ⟨193, 127, 6060⟩, ⟨193, 133, 729⟩, ⟨193, 139, 42⟩,
    ⟨193, 145, 337⟩, ⟨193, 151, 3584⟩, ⟨193, 157, 10103⟩, ⟨193, 163, 10272⟩,
    ⟨193, 169, 3554⟩, ⟨193, 175, 321⟩, ⟨193, 181, 848⟩, ⟨193, 187, 3518⟩,
    ⟨193, 193, 5635⟩, ⟨193, 199, 3514⟩, ⟨193, 205, 785⟩, ⟨193, 211, 352⟩,
    ⟨193, 217, 767⟩, ⟨193, 223, 825⟩, ⟨193, 229, 343⟩, ⟨193, 235, 39⟩,
    ⟨193, 241, 54⟩, ⟨193, 247, 44⟩, ⟨193, 253, 7⟩, ⟨193, 259, 8⟩,
    ⟨193, 265, 5⟩, ⟨199, 1, 3⟩, ⟨199, 7, 5⟩, ⟨199, 13, 28⟩,
    ⟨199, 19, 227⟩, ⟨199, 25, 545⟩, ⟨199, 31, 223⟩, ⟨199, 37, 26⟩,
    ⟨199, 43, 5⟩, ⟨199, 49, 3⟩, ⟨199, 55, 4⟩, ⟨199, 61, 34⟩,
    ⟨199, 67, 484⟩, ⟨199, 73, 2401⟩, ⟨199, 79, 2401⟩, ⟨199, 85, 495⟩,
    ⟨199, 91, 35⟩, ⟨199, 97, 5⟩, ⟨199, 103, 25⟩, ⟨199, 109, 473⟩,
    ⟨199, 115, 3454⟩, ⟨199, 121, 6401⟩, ⟨199, 127, 3814⟩, ⟨199, 133, 510⟩,
    ⟨199, 139, 28⟩, ⟨199, 145, 221⟩, ⟨199, 151, 2195⟩, ⟨199, 157, 6195⟩,
    ⟨199, 163, 6530⟩, ⟨199, 169, 2379⟩, ⟨199, 175, 214⟩, ⟨199, 181, 543⟩,
    ⟨199, 187, 2201⟩, ⟨199, 193, 3586⟩, ⟨199, 199, 2348⟩, ⟨199, 205, 550⟩,
    ⟨199, 211, 214⟩, ⟨199, 217, 502⟩, ⟨199, 223, 517⟩, ⟨199, 229, 230⟩,
    ⟨199, 235, 25⟩, ⟨199, 241, 35⟩, ⟨199, 247, 27⟩, ⟨199, 253, 4⟩,
    ⟨199, 259, 5⟩, ⟨199, 265, 3⟩, ⟨205, 1, 1⟩, ⟨205, 7, 1⟩,
    ⟨205, 13, 6⟩, ⟨205, 19, 54⟩, ⟨205, 25, 134⟩, ⟨205, 31, 52⟩,
    ⟨205, 37, 6⟩, ⟨205, 43, 1⟩, ⟨205, 55, 1⟩, ⟨205, 61, 8⟩,
    ⟨205, 67, 110⟩, ⟨205, 73, 545⟩, ⟨205, 79, 565⟩, ⟨205, 85, 115⟩,
    ⟨205, 91, 8⟩, ⟨205, 103, 6⟩, ⟨205, 109, 113⟩, ⟨205, 115, 786⟩,
    ⟨205, 121, 1400⟩, ⟨205, 127, 841⟩, ⟨205, 133, 116⟩, ⟨205, 145, 50⟩,
    ⟨205, 151, 488⟩, ⟨205, 157, 1345⟩, ⟨205, 163, 1409⟩, ⟨205, 169, 524⟩,
    ⟨205, 181, 126⟩, ⟨205, 187, 501⟩, ⟨205, 193, 827⟩, ⟨205, 199, 541⟩,
    ⟨205, 211, 50⟩, ⟨205, 217, 113⟩, ⟨205, 223, 114⟩, ⟨205, 235, 6⟩,
    ⟨205, 241, 8⟩, ⟨205, 253, 1⟩, ⟨211, 7, 1⟩, ⟨211, 13, 3⟩,
    ⟨211, 19, 22⟩, ⟨211, 25, 56⟩, ⟨211, 31, 22⟩, ⟨211, 37, 3⟩,
    ⟨211, 43, 1⟩, ⟨211, 61, 4⟩, ⟨211, 67, 50⟩, ⟨211, 73, 225⟩,
    ⟨211, 79, 230⟩, ⟨211, 85, 46⟩, ⟨211, 91, 3⟩, ⟨211, 97, 1⟩,
    ⟨211, 109, 50⟩, ⟨211, 115, 353⟩, ⟨211, 121, 633⟩, ⟨211, 127, 351⟩,
    ⟨211, 133, 47⟩, ⟨211, 139, 3⟩, ⟨211, 151, 227⟩, ⟨211, 157, 618⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 1408 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk11
