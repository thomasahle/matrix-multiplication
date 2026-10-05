import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk15

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntriesFirst : List TopScatterEntry := [
    ⟨124, 112, 1⟩, ⟨124, 118, 8⟩, ⟨124, 124, 14⟩, ⟨124, 130, 8⟩,
    ⟨124, 136, 1⟩, ⟨124, 154, 5⟩, ⟨124, 160, 13⟩, ⟨124, 166, 14⟩,
    ⟨124, 172, 5⟩, ⟨124, 184, 1⟩, ⟨124, 190, 5⟩, ⟨124, 196, 8⟩,
    ⟨124, 202, 5⟩, ⟨124, 208, 1⟩, ⟨124, 220, 1⟩, ⟨124, 226, 1⟩,
    ⟨130, 70, 1⟩, ⟨130, 76, 3⟩, ⟨130, 82, 3⟩, ⟨130, 88, 1⟩,
    ⟨130, 112, 1⟩, ⟨130, 118, 5⟩, ⟨130, 124, 8⟩, ⟨130, 130, 5⟩,
    ⟨130, 136, 1⟩, ⟨130, 154, 3⟩, ⟨130, 160, 8⟩, ⟨130, 166, 8⟩,
    ⟨130, 172, 3⟩, ⟨130, 190, 3⟩, ⟨130, 196, 5⟩, ⟨130, 202, 3⟩,
    ⟨130, 220, 1⟩, ⟨130, 226, 1⟩, ⟨136, 76, 1⟩, ⟨136, 82, 1⟩,
    ⟨136, 118, 1⟩, ⟨136, 124, 1⟩, ⟨136, 130, 1⟩, ⟨136, 154, 1⟩,
    ⟨136, 160, 1⟩, ⟨136, 166, 1⟩, ⟨136, 172, 1⟩, ⟨136, 190, 1⟩,
    ⟨136, 196, 1⟩, ⟨136, 202, 1⟩, ⟨154, 70, 1⟩, ⟨154, 76, 2⟩,
    ⟨154, 82, 2⟩, ⟨154, 88, 1⟩, ⟨154, 112, 1⟩, ⟨154, 118, 3⟩,
    ⟨154, 124, 5⟩, ⟨154, 130, 3⟩, ⟨154, 136, 1⟩, ⟨154, 154, 2⟩,
    ⟨154, 160, 5⟩, ⟨154, 166, 5⟩, ⟨154, 172, 2⟩, ⟨154, 190, 2⟩,
    ⟨154, 196, 3⟩, ⟨154, 202, 2⟩, ⟨154, 220, 1⟩, ⟨154, 226, 1⟩
  ]

def expectedEntriesSecond : List TopScatterEntry := [
    ⟨160, 28, 1⟩, ⟨160, 70, 1⟩, ⟨160, 76, 5⟩, ⟨160, 82, 5⟩,
    ⟨160, 88, 1⟩, ⟨160, 112, 1⟩, ⟨160, 118, 8⟩, ⟨160, 124, 13⟩,
    ⟨160, 130, 8⟩, ⟨160, 136, 1⟩, ⟨160, 154, 5⟩, ⟨160, 160, 14⟩,
    ⟨160, 166, 14⟩, ⟨160, 172, 5⟩, ⟨160, 184, 1⟩, ⟨160, 190, 5⟩,
    ⟨160, 196, 8⟩, ⟨160, 202, 5⟩, ⟨160, 208, 1⟩, ⟨160, 220, 1⟩,
    ⟨160, 226, 1⟩, ⟨166, 28, 1⟩, ⟨166, 70, 1⟩, ⟨166, 76, 5⟩,
    ⟨166, 82, 5⟩, ⟨166, 88, 1⟩, ⟨166, 112, 1⟩, ⟨166, 118, 8⟩,
    ⟨166, 124, 14⟩, ⟨166, 130, 8⟩, ⟨166, 136, 1⟩, ⟨166, 154, 5⟩,
    ⟨166, 160, 14⟩, ⟨166, 166, 14⟩, ⟨166, 172, 5⟩, ⟨166, 184, 1⟩,
    ⟨166, 190, 5⟩, ⟨166, 196, 8⟩, ⟨166, 202, 5⟩, ⟨166, 208, 1⟩,
    ⟨166, 220, 1⟩, ⟨166, 226, 1⟩, ⟨172, 70, 1⟩, ⟨172, 76, 2⟩,
    ⟨172, 82, 2⟩, ⟨172, 88, 1⟩, ⟨172, 112, 1⟩, ⟨172, 118, 3⟩,
    ⟨172, 124, 5⟩, ⟨172, 130, 3⟩, ⟨172, 136, 1⟩, ⟨172, 154, 2⟩,
    ⟨172, 160, 5⟩, ⟨172, 166, 5⟩, ⟨172, 172, 2⟩, ⟨172, 190, 2⟩,
    ⟨172, 196, 3⟩, ⟨172, 202, 2⟩, ⟨172, 220, 1⟩, ⟨172, 226, 1⟩,
    ⟨184, 124, 1⟩, ⟨184, 160, 1⟩, ⟨184, 166, 1⟩, ⟨190, 70, 1⟩
  ]

def expectedEntries : List TopScatterEntry := expectedEntriesFirst ++ expectedEntriesSecond

opaque recurrence_first :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 1920 64 = expectedEntriesFirst := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

opaque recurrence_second :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 1984 64 = expectedEntriesSecond := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

theorem recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 1920 128 = expectedEntries := by
  calc
    _ = topScatteredEntryRangeWithPairs generatedPrimaryTables
          PairGeometry.expectedIndices 1920 64 ++
        topScatteredEntryRangeWithPairs generatedPrimaryTables
          PairGeometry.expectedIndices 1984 64 := by
      unfold topScatteredEntryRangeWithPairs
      rw [show 128 = 64 + 64 by rfl, List.take_add,
        List.filterMap_append, List.drop_drop]
    _ = expectedEntries := by
      rw [recurrence_first, recurrence_second]
      rfl

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk15
