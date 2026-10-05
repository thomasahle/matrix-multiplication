import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk14

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntriesFirst : List TopScatterEntry := [
    ⟨259, 151, 5⟩, ⟨259, 157, 14⟩, ⟨259, 163, 14⟩, ⟨259, 169, 5⟩,
    ⟨259, 181, 1⟩, ⟨259, 187, 5⟩, ⟨259, 193, 8⟩, ⟨259, 199, 5⟩,
    ⟨259, 211, 1⟩, ⟨259, 217, 1⟩, ⟨259, 223, 1⟩, ⟨265, 25, 1⟩,
    ⟨265, 67, 1⟩, ⟨265, 73, 3⟩, ⟨265, 79, 3⟩, ⟨265, 85, 1⟩,
    ⟨265, 109, 1⟩, ⟨265, 115, 5⟩, ⟨265, 121, 9⟩, ⟨265, 127, 5⟩,
    ⟨265, 133, 1⟩, ⟨265, 151, 3⟩, ⟨265, 157, 9⟩, ⟨265, 163, 8⟩,
    ⟨265, 169, 3⟩, ⟨265, 187, 3⟩, ⟨265, 193, 5⟩, ⟨265, 199, 3⟩,
    ⟨265, 217, 1⟩, ⟨265, 223, 1⟩, ⟨28, 124, 1⟩, ⟨28, 160, 1⟩,
    ⟨28, 166, 1⟩, ⟨70, 76, 1⟩, ⟨70, 82, 1⟩, ⟨70, 118, 1⟩,
    ⟨70, 124, 1⟩, ⟨70, 130, 1⟩, ⟨70, 154, 1⟩, ⟨70, 160, 1⟩,
    ⟨70, 166, 1⟩, ⟨70, 172, 1⟩, ⟨70, 190, 1⟩, ⟨70, 196, 1⟩,
    ⟨70, 202, 1⟩, ⟨76, 70, 1⟩, ⟨76, 76, 2⟩, ⟨76, 82, 2⟩,
    ⟨76, 88, 1⟩, ⟨76, 112, 1⟩, ⟨76, 118, 3⟩, ⟨76, 124, 5⟩,
    ⟨76, 130, 3⟩, ⟨76, 136, 1⟩, ⟨76, 154, 2⟩, ⟨76, 160, 5⟩,
    ⟨76, 166, 5⟩, ⟨76, 172, 2⟩, ⟨76, 190, 2⟩, ⟨76, 196, 3⟩,
    ⟨76, 202, 2⟩, ⟨76, 220, 1⟩, ⟨76, 226, 1⟩, ⟨82, 70, 1⟩
  ]

def expectedEntriesSecond : List TopScatterEntry := [
    ⟨82, 76, 2⟩, ⟨82, 82, 2⟩, ⟨82, 88, 1⟩, ⟨82, 112, 1⟩,
    ⟨82, 118, 3⟩, ⟨82, 124, 5⟩, ⟨82, 130, 3⟩, ⟨82, 136, 1⟩,
    ⟨82, 154, 2⟩, ⟨82, 160, 5⟩, ⟨82, 166, 5⟩, ⟨82, 172, 2⟩,
    ⟨82, 190, 2⟩, ⟨82, 196, 3⟩, ⟨82, 202, 2⟩, ⟨82, 220, 1⟩,
    ⟨82, 226, 1⟩, ⟨88, 76, 1⟩, ⟨88, 82, 1⟩, ⟨88, 118, 1⟩,
    ⟨88, 124, 1⟩, ⟨88, 130, 1⟩, ⟨88, 154, 1⟩, ⟨88, 160, 1⟩,
    ⟨88, 166, 1⟩, ⟨88, 172, 1⟩, ⟨88, 190, 1⟩, ⟨88, 196, 1⟩,
    ⟨88, 202, 1⟩, ⟨112, 76, 1⟩, ⟨112, 82, 1⟩, ⟨112, 118, 1⟩,
    ⟨112, 124, 1⟩, ⟨112, 130, 1⟩, ⟨112, 154, 1⟩, ⟨112, 160, 1⟩,
    ⟨112, 166, 1⟩, ⟨112, 172, 1⟩, ⟨112, 190, 1⟩, ⟨112, 196, 1⟩,
    ⟨112, 202, 1⟩, ⟨118, 70, 1⟩, ⟨118, 76, 3⟩, ⟨118, 82, 3⟩,
    ⟨118, 88, 1⟩, ⟨118, 112, 1⟩, ⟨118, 118, 5⟩, ⟨118, 124, 8⟩,
    ⟨118, 130, 5⟩, ⟨118, 136, 1⟩, ⟨118, 154, 3⟩, ⟨118, 160, 8⟩,
    ⟨118, 166, 8⟩, ⟨118, 172, 3⟩, ⟨118, 190, 3⟩, ⟨118, 196, 5⟩,
    ⟨118, 202, 3⟩, ⟨118, 220, 1⟩, ⟨118, 226, 1⟩, ⟨124, 28, 1⟩,
    ⟨124, 70, 1⟩, ⟨124, 76, 5⟩, ⟨124, 82, 5⟩, ⟨124, 88, 1⟩
  ]

def expectedEntries : List TopScatterEntry := expectedEntriesFirst ++ expectedEntriesSecond

opaque recurrence_first :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 1792 64 = expectedEntriesFirst := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

opaque recurrence_second :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 1856 64 = expectedEntriesSecond := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

theorem recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 1792 128 = expectedEntries := by
  calc
    _ = topScatteredEntryRangeWithPairs generatedPrimaryTables
          PairGeometry.expectedIndices 1792 64 ++
        topScatteredEntryRangeWithPairs generatedPrimaryTables
          PairGeometry.expectedIndices 1856 64 := by
      unfold topScatteredEntryRangeWithPairs
      rw [show 128 = 64 + 64 by rfl, List.take_add,
        List.filterMap_append, List.drop_drop]
    _ = expectedEntries := by
      rw [recurrence_first, recurrence_second]
      rfl

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk14
