import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk7

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨115, 247, 43⟩, ⟨115, 253, 7⟩, ⟨115, 259, 8⟩, ⟨115, 265, 5⟩,
    ⟨121, 1, 9⟩, ⟨121, 7, 12⟩, ⟨121, 13, 71⟩, ⟨121, 19, 587⟩,
    ⟨121, 25, 1461⟩, ⟨121, 31, 584⟩, ⟨121, 37, 70⟩, ⟨121, 43, 13⟩,
    ⟨121, 49, 9⟩, ⟨121, 55, 11⟩, ⟨121, 61, 93⟩, ⟨121, 67, 1294⟩,
    ⟨121, 73, 6036⟩, ⟨121, 79, 6086⟩, ⟨121, 85, 1260⟩, ⟨121, 91, 89⟩,
    ⟨121, 97, 13⟩, ⟨121, 103, 68⟩, ⟨121, 109, 1218⟩, ⟨121, 115, 8811⟩,
    ⟨121, 121, 16137⟩, ⟨121, 127, 9082⟩, ⟨121, 133, 1254⟩, ⟨121, 139, 71⟩,
    ⟨121, 145, 571⟩, ⟨121, 151, 5571⟩, ⟨121, 157, 15961⟩, ⟨121, 163, 16999⟩,
    ⟨121, 169, 5864⟩, ⟨121, 175, 566⟩, ⟨121, 181, 1486⟩, ⟨121, 187, 6158⟩,
    ⟨121, 193, 10432⟩, ⟨121, 199, 6526⟩, ⟨121, 205, 1448⟩, ⟨121, 211, 621⟩,
    ⟨121, 217, 1418⟩, ⟨121, 223, 1490⟩, ⟨121, 229, 617⟩, ⟨121, 235, 67⟩,
    ⟨121, 241, 94⟩, ⟨121, 247, 75⟩, ⟨121, 253, 11⟩, ⟨121, 259, 13⟩,
    ⟨121, 265, 8⟩, ⟨127, 1, 5⟩, ⟨127, 7, 7⟩, ⟨127, 13, 40⟩,
    ⟨127, 19, 337⟩, ⟨127, 25, 823⟩, ⟨127, 31, 331⟩, ⟨127, 37, 40⟩,
    ⟨127, 43, 7⟩, ⟨127, 49, 5⟩, ⟨127, 55, 6⟩, ⟨127, 61, 53⟩,
    ⟨127, 67, 766⟩, ⟨127, 73, 3363⟩, ⟨127, 79, 3543⟩, ⟨127, 85, 739⟩,
    ⟨127, 91, 52⟩, ⟨127, 97, 8⟩, ⟨127, 103, 40⟩, ⟨127, 109, 717⟩,
    ⟨127, 115, 5037⟩, ⟨127, 121, 9152⟩, ⟨127, 127, 5370⟩, ⟨127, 133, 746⟩,
    ⟨127, 139, 40⟩, ⟨127, 145, 331⟩, ⟨127, 151, 3096⟩, ⟨127, 157, 8850⟩,
    ⟨127, 163, 9816⟩, ⟨127, 169, 3456⟩, ⟨127, 175, 333⟩, ⟨127, 181, 830⟩,
    ⟨127, 187, 3458⟩, ⟨127, 193, 5937⟩, ⟨127, 199, 3825⟩, ⟨127, 205, 846⟩,
    ⟨127, 211, 348⟩, ⟨127, 217, 825⟩, ⟨127, 223, 793⟩, ⟨127, 229, 346⟩,
    ⟨127, 235, 42⟩, ⟨127, 241, 57⟩, ⟨127, 247, 43⟩, ⟨127, 253, 7⟩,
    ⟨127, 259, 8⟩, ⟨127, 265, 5⟩, ⟨133, 1, 1⟩, ⟨133, 7, 1⟩,
    ⟨133, 13, 6⟩, ⟨133, 19, 46⟩, ⟨133, 25, 114⟩, ⟨133, 31, 46⟩,
    ⟨133, 37, 6⟩, ⟨133, 43, 1⟩, ⟨133, 49, 1⟩, ⟨133, 55, 1⟩,
    ⟨133, 61, 7⟩, ⟨133, 67, 103⟩, ⟨133, 73, 477⟩, ⟨133, 79, 486⟩,
    ⟨133, 85, 104⟩, ⟨133, 91, 7⟩, ⟨133, 97, 1⟩, ⟨133, 103, 6⟩,
    ⟨133, 109, 100⟩, ⟨133, 115, 674⟩, ⟨133, 121, 1214⟩, ⟨133, 127, 752⟩,
    ⟨133, 133, 99⟩, ⟨133, 139, 6⟩, ⟨133, 145, 47⟩, ⟨133, 151, 465⟩,
    ⟨133, 157, 1218⟩, ⟨133, 163, 1246⟩, ⟨133, 169, 466⟩, ⟨133, 175, 47⟩,
    ⟨133, 181, 115⟩, ⟨133, 187, 450⟩, ⟨133, 193, 761⟩, ⟨133, 199, 488⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 896 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk7
