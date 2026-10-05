import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk16

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntriesFirst : List TopScatterEntry := [
    ⟨190, 76, 2⟩, ⟨190, 82, 2⟩, ⟨190, 88, 1⟩, ⟨190, 112, 1⟩,
    ⟨190, 118, 3⟩, ⟨190, 124, 5⟩, ⟨190, 130, 3⟩, ⟨190, 136, 1⟩,
    ⟨190, 154, 2⟩, ⟨190, 160, 5⟩, ⟨190, 166, 5⟩, ⟨190, 172, 2⟩,
    ⟨190, 190, 2⟩, ⟨190, 196, 3⟩, ⟨190, 202, 2⟩, ⟨190, 220, 1⟩,
    ⟨190, 226, 1⟩, ⟨196, 70, 1⟩, ⟨196, 76, 3⟩, ⟨196, 82, 3⟩,
    ⟨196, 88, 1⟩, ⟨196, 112, 1⟩, ⟨196, 118, 5⟩, ⟨196, 124, 8⟩,
    ⟨196, 130, 5⟩, ⟨196, 136, 1⟩, ⟨196, 154, 3⟩, ⟨196, 160, 8⟩,
    ⟨196, 166, 8⟩, ⟨196, 172, 3⟩, ⟨196, 190, 3⟩, ⟨196, 196, 5⟩,
    ⟨196, 202, 3⟩, ⟨196, 220, 1⟩, ⟨196, 226, 1⟩, ⟨202, 70, 1⟩,
    ⟨202, 76, 2⟩, ⟨202, 82, 2⟩, ⟨202, 88, 1⟩, ⟨202, 112, 1⟩,
    ⟨202, 118, 3⟩, ⟨202, 124, 5⟩, ⟨202, 130, 3⟩, ⟨202, 136, 1⟩,
    ⟨202, 154, 2⟩, ⟨202, 160, 5⟩, ⟨202, 166, 5⟩, ⟨202, 172, 2⟩,
    ⟨202, 190, 2⟩, ⟨202, 196, 3⟩, ⟨202, 202, 2⟩, ⟨202, 220, 1⟩,
    ⟨202, 226, 1⟩, ⟨208, 124, 1⟩, ⟨208, 160, 1⟩, ⟨208, 166, 1⟩,
    ⟨220, 76, 1⟩, ⟨220, 82, 1⟩, ⟨220, 118, 1⟩, ⟨220, 124, 1⟩,
    ⟨220, 130, 1⟩, ⟨220, 154, 1⟩, ⟨220, 160, 1⟩, ⟨220, 166, 1⟩
  ]

def expectedEntriesSecond : List TopScatterEntry := [
    ⟨220, 172, 1⟩, ⟨220, 190, 1⟩, ⟨220, 196, 1⟩, ⟨220, 202, 1⟩,
    ⟨226, 76, 1⟩, ⟨226, 82, 1⟩, ⟨226, 118, 1⟩, ⟨226, 124, 1⟩,
    ⟨226, 130, 1⟩, ⟨226, 154, 1⟩, ⟨226, 160, 1⟩, ⟨226, 166, 1⟩,
    ⟨226, 172, 1⟩, ⟨226, 190, 1⟩, ⟨226, 196, 1⟩, ⟨226, 202, 1⟩,
    ⟨71, 125, 1⟩, ⟨71, 161, 1⟩, ⟨71, 167, 1⟩, ⟨77, 77, 1⟩,
    ⟨77, 83, 1⟩, ⟨77, 119, 1⟩, ⟨77, 125, 2⟩, ⟨77, 131, 1⟩,
    ⟨77, 155, 1⟩, ⟨77, 161, 2⟩, ⟨77, 167, 2⟩, ⟨77, 173, 1⟩,
    ⟨77, 191, 1⟩, ⟨77, 197, 1⟩, ⟨77, 203, 1⟩, ⟨83, 77, 1⟩,
    ⟨83, 83, 1⟩, ⟨83, 119, 1⟩, ⟨83, 125, 2⟩, ⟨83, 131, 1⟩,
    ⟨83, 155, 1⟩, ⟨83, 161, 2⟩, ⟨83, 167, 2⟩, ⟨83, 173, 1⟩,
    ⟨83, 191, 1⟩, ⟨83, 197, 1⟩, ⟨83, 203, 1⟩, ⟨89, 125, 1⟩,
    ⟨89, 161, 1⟩, ⟨89, 167, 1⟩, ⟨113, 125, 1⟩, ⟨113, 161, 1⟩,
    ⟨113, 167, 1⟩, ⟨119, 77, 1⟩, ⟨119, 83, 1⟩, ⟨119, 119, 2⟩,
    ⟨119, 125, 3⟩, ⟨119, 131, 2⟩, ⟨119, 155, 1⟩, ⟨119, 161, 3⟩,
    ⟨119, 167, 3⟩, ⟨119, 173, 1⟩, ⟨119, 191, 1⟩, ⟨119, 197, 2⟩,
    ⟨119, 203, 1⟩, ⟨125, 71, 1⟩, ⟨125, 77, 2⟩, ⟨125, 83, 2⟩
  ]

def expectedEntries : List TopScatterEntry := expectedEntriesFirst ++ expectedEntriesSecond

opaque recurrence_first :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 2048 64 = expectedEntriesFirst := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

opaque recurrence_second :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 2112 64 = expectedEntriesSecond := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

theorem recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 2048 128 = expectedEntries := by
  calc
    _ = topScatteredEntryRangeWithPairs generatedPrimaryTables
          PairGeometry.expectedIndices 2048 64 ++
        topScatteredEntryRangeWithPairs generatedPrimaryTables
          PairGeometry.expectedIndices 2112 64 := by
      unfold topScatteredEntryRangeWithPairs
      rw [show 128 = 64 + 64 by rfl, List.take_add,
        List.filterMap_append, List.drop_drop]
    _ = expectedEntries := by
      rw [recurrence_first, recurrence_second]
      rfl

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk16
