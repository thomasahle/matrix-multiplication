import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk0

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨66, 114, 1⟩, ⟨66, 120, 1⟩, ⟨66, 126, 1⟩, ⟨66, 156, 1⟩,
    ⟨66, 162, 1⟩, ⟨66, 192, 1⟩, ⟨72, 72, 1⟩, ⟨72, 78, 1⟩,
    ⟨72, 114, 2⟩, ⟨72, 120, 3⟩, ⟨72, 126, 2⟩, ⟨72, 150, 1⟩,
    ⟨72, 156, 3⟩, ⟨72, 162, 3⟩, ⟨72, 168, 1⟩, ⟨72, 186, 1⟩,
    ⟨72, 192, 2⟩, ⟨72, 198, 1⟩, ⟨78, 72, 1⟩, ⟨78, 78, 1⟩,
    ⟨78, 114, 2⟩, ⟨78, 120, 3⟩, ⟨78, 126, 2⟩, ⟨78, 150, 1⟩,
    ⟨78, 156, 3⟩, ⟨78, 162, 3⟩, ⟨78, 168, 1⟩, ⟨78, 186, 1⟩,
    ⟨78, 192, 2⟩, ⟨78, 198, 1⟩, ⟨84, 114, 1⟩, ⟨84, 120, 1⟩,
    ⟨84, 126, 1⟩, ⟨84, 156, 1⟩, ⟨84, 162, 1⟩, ⟨84, 192, 1⟩,
    ⟨108, 114, 1⟩, ⟨108, 120, 1⟩, ⟨108, 126, 1⟩, ⟨108, 156, 1⟩,
    ⟨108, 162, 1⟩, ⟨108, 192, 1⟩, ⟨114, 66, 1⟩, ⟨114, 72, 2⟩,
    ⟨114, 78, 2⟩, ⟨114, 84, 1⟩, ⟨114, 108, 1⟩, ⟨114, 114, 3⟩,
    ⟨114, 120, 5⟩, ⟨114, 126, 3⟩, ⟨114, 132, 1⟩, ⟨114, 150, 2⟩,
    ⟨114, 156, 5⟩, ⟨114, 162, 5⟩, ⟨114, 168, 2⟩, ⟨114, 186, 2⟩,
    ⟨114, 192, 3⟩, ⟨114, 198, 2⟩, ⟨114, 216, 1⟩, ⟨114, 222, 1⟩,
    ⟨120, 66, 1⟩, ⟨120, 72, 3⟩, ⟨120, 78, 3⟩, ⟨120, 84, 1⟩,
    ⟨120, 108, 1⟩, ⟨120, 114, 5⟩, ⟨120, 120, 9⟩, ⟨120, 126, 5⟩,
    ⟨120, 132, 1⟩, ⟨120, 150, 3⟩, ⟨120, 156, 9⟩, ⟨120, 162, 9⟩,
    ⟨120, 168, 3⟩, ⟨120, 180, 1⟩, ⟨120, 186, 3⟩, ⟨120, 192, 5⟩,
    ⟨120, 198, 3⟩, ⟨120, 216, 1⟩, ⟨120, 222, 1⟩, ⟨126, 66, 1⟩,
    ⟨126, 72, 2⟩, ⟨126, 78, 2⟩, ⟨126, 84, 1⟩, ⟨126, 108, 1⟩,
    ⟨126, 114, 3⟩, ⟨126, 120, 5⟩, ⟨126, 126, 3⟩, ⟨126, 132, 1⟩,
    ⟨126, 150, 2⟩, ⟨126, 156, 6⟩, ⟨126, 162, 5⟩, ⟨126, 168, 2⟩,
    ⟨126, 186, 2⟩, ⟨126, 192, 3⟩, ⟨126, 198, 2⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 0 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk0
