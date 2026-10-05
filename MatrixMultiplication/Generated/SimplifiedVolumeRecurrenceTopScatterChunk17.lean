import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk17

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntriesFirst : List TopScatterEntry := [
    ⟨125, 89, 1⟩, ⟨125, 113, 1⟩, ⟨125, 119, 3⟩, ⟨125, 125, 5⟩,
    ⟨125, 131, 3⟩, ⟨125, 137, 1⟩, ⟨125, 155, 2⟩, ⟨125, 161, 6⟩,
    ⟨125, 167, 5⟩, ⟨125, 173, 2⟩, ⟨125, 191, 2⟩, ⟨125, 197, 3⟩,
    ⟨125, 203, 2⟩, ⟨125, 221, 1⟩, ⟨125, 227, 1⟩, ⟨131, 77, 1⟩,
    ⟨131, 83, 1⟩, ⟨131, 119, 2⟩, ⟨131, 125, 3⟩, ⟨131, 131, 2⟩,
    ⟨131, 155, 1⟩, ⟨131, 161, 3⟩, ⟨131, 167, 3⟩, ⟨131, 173, 1⟩,
    ⟨131, 191, 1⟩, ⟨131, 197, 2⟩, ⟨131, 203, 1⟩, ⟨137, 125, 1⟩,
    ⟨137, 161, 1⟩, ⟨137, 167, 1⟩, ⟨155, 77, 1⟩, ⟨155, 83, 1⟩,
    ⟨155, 119, 1⟩, ⟨155, 125, 2⟩, ⟨155, 131, 1⟩, ⟨155, 155, 1⟩,
    ⟨155, 161, 2⟩, ⟨155, 167, 2⟩, ⟨155, 173, 1⟩, ⟨155, 191, 1⟩,
    ⟨155, 197, 1⟩, ⟨155, 203, 1⟩, ⟨161, 71, 1⟩, ⟨161, 77, 2⟩,
    ⟨161, 83, 2⟩, ⟨161, 89, 1⟩, ⟨161, 113, 1⟩, ⟨161, 119, 3⟩,
    ⟨161, 125, 6⟩, ⟨161, 131, 3⟩, ⟨161, 137, 1⟩, ⟨161, 155, 2⟩,
    ⟨161, 161, 6⟩, ⟨161, 167, 6⟩, ⟨161, 173, 2⟩, ⟨161, 191, 2⟩,
    ⟨161, 197, 3⟩, ⟨161, 203, 2⟩, ⟨161, 221, 1⟩, ⟨161, 227, 1⟩,
    ⟨167, 71, 1⟩, ⟨167, 77, 2⟩, ⟨167, 83, 2⟩, ⟨167, 89, 1⟩
  ]

def expectedEntriesSecond : List TopScatterEntry := [
    ⟨167, 113, 1⟩, ⟨167, 119, 3⟩, ⟨167, 125, 5⟩, ⟨167, 131, 3⟩,
    ⟨167, 137, 1⟩, ⟨167, 155, 2⟩, ⟨167, 161, 6⟩, ⟨167, 167, 5⟩,
    ⟨167, 173, 2⟩, ⟨167, 191, 2⟩, ⟨167, 197, 3⟩, ⟨167, 203, 2⟩,
    ⟨167, 221, 1⟩, ⟨167, 227, 1⟩, ⟨173, 77, 1⟩, ⟨173, 83, 1⟩,
    ⟨173, 119, 1⟩, ⟨173, 125, 2⟩, ⟨173, 131, 1⟩, ⟨173, 155, 1⟩,
    ⟨173, 161, 2⟩, ⟨173, 167, 2⟩, ⟨173, 173, 1⟩, ⟨173, 191, 1⟩,
    ⟨173, 197, 1⟩, ⟨173, 203, 1⟩, ⟨191, 77, 1⟩, ⟨191, 83, 1⟩,
    ⟨191, 119, 1⟩, ⟨191, 125, 2⟩, ⟨191, 131, 1⟩, ⟨191, 155, 1⟩,
    ⟨191, 161, 2⟩, ⟨191, 167, 2⟩, ⟨191, 173, 1⟩, ⟨191, 191, 1⟩,
    ⟨191, 197, 1⟩, ⟨191, 203, 1⟩, ⟨197, 77, 1⟩, ⟨197, 83, 1⟩,
    ⟨197, 119, 2⟩, ⟨197, 125, 3⟩, ⟨197, 131, 2⟩, ⟨197, 155, 1⟩,
    ⟨197, 161, 3⟩, ⟨197, 167, 3⟩, ⟨197, 173, 1⟩, ⟨197, 191, 1⟩,
    ⟨197, 197, 2⟩, ⟨197, 203, 1⟩, ⟨203, 77, 1⟩, ⟨203, 83, 1⟩,
    ⟨203, 119, 1⟩, ⟨203, 125, 2⟩, ⟨203, 131, 1⟩, ⟨203, 155, 1⟩,
    ⟨203, 161, 2⟩, ⟨203, 167, 2⟩, ⟨203, 173, 1⟩, ⟨203, 191, 1⟩,
    ⟨203, 197, 1⟩, ⟨203, 203, 1⟩, ⟨221, 125, 1⟩, ⟨221, 161, 1⟩
  ]

def expectedEntries : List TopScatterEntry := expectedEntriesFirst ++ expectedEntriesSecond

opaque recurrence_first :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 2176 64 = expectedEntriesFirst := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

opaque recurrence_second :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 2240 64 = expectedEntriesSecond := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide +kernel

theorem recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 2176 128 = expectedEntries := by
  calc
    _ = topScatteredEntryRangeWithPairs generatedPrimaryTables
          PairGeometry.expectedIndices 2176 64 ++
        topScatteredEntryRangeWithPairs generatedPrimaryTables
          PairGeometry.expectedIndices 2240 64 := by
      unfold topScatteredEntryRangeWithPairs
      rw [show 128 = 64 + 64 by rfl, List.take_add,
        List.filterMap_append, List.drop_drop]
    _ = expectedEntries := by
      rw [recurrence_first, recurrence_second]
      rfl

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk17
