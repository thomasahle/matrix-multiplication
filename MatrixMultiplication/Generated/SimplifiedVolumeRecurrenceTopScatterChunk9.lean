import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk9

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨157, 79, 6097⟩, ⟨157, 85, 1242⟩, ⟨157, 91, 86⟩, ⟨157, 97, 13⟩,
    ⟨157, 103, 70⟩, ⟨157, 109, 1294⟩, ⟨157, 115, 9442⟩, ⟨157, 121, 16485⟩,
    ⟨157, 127, 9158⟩, ⟨157, 133, 1198⟩, ⟨157, 139, 68⟩, ⟨157, 145, 590⟩,
    ⟨157, 151, 5757⟩, ⟨157, 157, 16086⟩, ⟨157, 163, 16357⟩, ⟨157, 169, 5512⟩,
    ⟨157, 175, 547⟩, ⟨157, 181, 1507⟩, ⟨157, 187, 6254⟩, ⟨157, 193, 10108⟩,
    ⟨157, 199, 5987⟩, ⟨157, 205, 1364⟩, ⟨157, 211, 621⟩, ⟨157, 217, 1358⟩,
    ⟨157, 223, 1432⟩, ⟨157, 229, 581⟩, ⟨157, 235, 68⟩, ⟨157, 241, 97⟩,
    ⟨157, 247, 72⟩, ⟨157, 253, 11⟩, ⟨157, 259, 14⟩, ⟨157, 265, 8⟩,
    ⟨163, 1, 9⟩, ⟨163, 7, 13⟩, ⟨163, 13, 72⟩, ⟨163, 19, 599⟩,
    ⟨163, 25, 1495⟩, ⟨163, 31, 617⟩, ⟨163, 37, 72⟩, ⟨163, 43, 13⟩,
    ⟨163, 49, 9⟩, ⟨163, 55, 11⟩, ⟨163, 61, 92⟩, ⟨163, 67, 1290⟩,
    ⟨163, 73, 6487⟩, ⟨163, 79, 6249⟩, ⟨163, 85, 1267⟩, ⟨163, 91, 88⟩,
    ⟨163, 97, 14⟩, ⟨163, 103, 69⟩, ⟨163, 109, 1197⟩, ⟨163, 115, 9082⟩,
    ⟨163, 121, 17607⟩, ⟨163, 127, 9797⟩, ⟨163, 133, 1244⟩, ⟨163, 139, 70⟩,
    ⟨163, 145, 589⟩, ⟨163, 151, 5723⟩, ⟨163, 157, 16236⟩, ⟨163, 163, 17532⟩,
    ⟨163, 169, 5927⟩, ⟨163, 175, 557⟩, ⟨163, 181, 1442⟩, ⟨163, 187, 5810⟩,
    ⟨163, 193, 10460⟩, ⟨163, 199, 6430⟩, ⟨163, 205, 1410⟩, ⟨163, 211, 625⟩,
    ⟨163, 217, 1390⟩, ⟨163, 223, 1407⟩, ⟨163, 229, 622⟩, ⟨163, 235, 69⟩,
    ⟨163, 241, 93⟩, ⟨163, 247, 75⟩, ⟨163, 253, 12⟩, ⟨163, 259, 14⟩,
    ⟨163, 265, 9⟩, ⟨169, 1, 3⟩, ⟨169, 7, 5⟩, ⟨169, 13, 27⟩,
    ⟨169, 19, 226⟩, ⟨169, 25, 544⟩, ⟨169, 31, 221⟩, ⟨169, 37, 26⟩,
    ⟨169, 43, 5⟩, ⟨169, 49, 3⟩, ⟨169, 55, 4⟩, ⟨169, 61, 35⟩,
    ⟨169, 67, 477⟩, ⟨169, 73, 2221⟩, ⟨169, 79, 2293⟩, ⟨169, 85, 465⟩,
    ⟨169, 91, 34⟩, ⟨169, 97, 5⟩, ⟨169, 103, 25⟩, ⟨169, 109, 454⟩,
    ⟨169, 115, 3180⟩, ⟨169, 121, 5816⟩, ⟨169, 127, 3574⟩, ⟨169, 133, 461⟩,
    ⟨169, 139, 27⟩, ⟨169, 145, 222⟩, ⟨169, 151, 1992⟩, ⟨169, 157, 5555⟩,
    ⟨169, 163, 5952⟩, ⟨169, 169, 2181⟩, ⟨169, 175, 212⟩, ⟨169, 181, 522⟩,
    ⟨169, 187, 2142⟩, ⟨169, 193, 3493⟩, ⟨169, 199, 2289⟩, ⟨169, 205, 528⟩,
    ⟨169, 211, 221⟩, ⟨169, 217, 503⟩, ⟨169, 223, 500⟩, ⟨169, 229, 222⟩,
    ⟨169, 235, 25⟩, ⟨169, 241, 34⟩, ⟨169, 247, 27⟩, ⟨169, 253, 4⟩,
    ⟨169, 259, 5⟩, ⟨169, 265, 3⟩, ⟨175, 7, 1⟩, ⟨175, 13, 3⟩,
    ⟨175, 19, 20⟩, ⟨175, 25, 50⟩, ⟨175, 31, 21⟩, ⟨175, 37, 3⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 1152 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk9
