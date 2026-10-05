import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk18

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntriesFirst : List TopScatterEntry := [
    ⟨221, 167, 1⟩, ⟨227, 125, 1⟩
  ]

def expectedEntriesSecond : List TopScatterEntry := [
    ⟨227, 161, 1⟩, ⟨227, 167, 1⟩
  ]

def expectedEntries : List TopScatterEntry := expectedEntriesFirst ++ expectedEntriesSecond

opaque recurrence_first :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 2304 2 = expectedEntriesFirst := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

opaque recurrence_second :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 2306 2 = expectedEntriesSecond := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

theorem recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 2304 4 = expectedEntries := by
  calc
    _ = topScatteredEntryRangeWithPairs generatedPrimaryTables
          PairGeometry.expectedIndices 2304 2 ++
        topScatteredEntryRangeWithPairs generatedPrimaryTables
          PairGeometry.expectedIndices 2306 2 := by
      unfold topScatteredEntryRangeWithPairs
      rw [show 4 = 2 + 2 by rfl, List.take_add,
        List.filterMap_append, List.drop_drop]
    _ = expectedEntries := by
      rw [recurrence_first, recurrence_second]
      rfl

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk18
