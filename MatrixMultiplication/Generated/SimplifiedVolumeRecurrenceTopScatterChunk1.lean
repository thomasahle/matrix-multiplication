import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk1

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨126, 216, 1⟩, ⟨126, 222, 1⟩, ⟨132, 114, 1⟩, ⟨132, 120, 1⟩,
    ⟨132, 126, 1⟩, ⟨132, 156, 1⟩, ⟨132, 162, 1⟩, ⟨132, 192, 1⟩,
    ⟨150, 72, 1⟩, ⟨150, 78, 1⟩, ⟨150, 114, 2⟩, ⟨150, 120, 3⟩,
    ⟨150, 126, 2⟩, ⟨150, 150, 1⟩, ⟨150, 156, 3⟩, ⟨150, 162, 3⟩,
    ⟨150, 168, 1⟩, ⟨150, 186, 1⟩, ⟨150, 192, 2⟩, ⟨150, 198, 1⟩,
    ⟨156, 66, 1⟩, ⟨156, 72, 3⟩, ⟨156, 78, 3⟩, ⟨156, 84, 1⟩,
    ⟨156, 108, 1⟩, ⟨156, 114, 5⟩, ⟨156, 120, 9⟩, ⟨156, 126, 6⟩,
    ⟨156, 132, 1⟩, ⟨156, 150, 3⟩, ⟨156, 156, 9⟩, ⟨156, 162, 9⟩,
    ⟨156, 168, 3⟩, ⟨156, 180, 1⟩, ⟨156, 186, 3⟩, ⟨156, 192, 5⟩,
    ⟨156, 198, 3⟩, ⟨156, 216, 1⟩, ⟨156, 222, 1⟩, ⟨162, 66, 1⟩,
    ⟨162, 72, 3⟩, ⟨162, 78, 3⟩, ⟨162, 84, 1⟩, ⟨162, 108, 1⟩,
    ⟨162, 114, 5⟩, ⟨162, 120, 9⟩, ⟨162, 126, 5⟩, ⟨162, 132, 1⟩,
    ⟨162, 150, 3⟩, ⟨162, 156, 9⟩, ⟨162, 162, 9⟩, ⟨162, 168, 3⟩,
    ⟨162, 180, 1⟩, ⟨162, 186, 3⟩, ⟨162, 192, 5⟩, ⟨162, 198, 3⟩,
    ⟨162, 216, 1⟩, ⟨162, 222, 1⟩, ⟨168, 72, 1⟩, ⟨168, 78, 1⟩,
    ⟨168, 114, 2⟩, ⟨168, 120, 3⟩, ⟨168, 126, 2⟩, ⟨168, 150, 1⟩,
    ⟨168, 156, 3⟩, ⟨168, 162, 3⟩, ⟨168, 168, 1⟩, ⟨168, 186, 1⟩,
    ⟨168, 192, 2⟩, ⟨168, 198, 1⟩, ⟨180, 120, 1⟩, ⟨180, 156, 1⟩,
    ⟨180, 162, 1⟩, ⟨186, 72, 1⟩, ⟨186, 78, 1⟩, ⟨186, 114, 2⟩,
    ⟨186, 120, 3⟩, ⟨186, 126, 2⟩, ⟨186, 150, 1⟩, ⟨186, 156, 3⟩,
    ⟨186, 162, 3⟩, ⟨186, 168, 1⟩, ⟨186, 186, 1⟩, ⟨186, 192, 2⟩,
    ⟨186, 198, 1⟩, ⟨192, 66, 1⟩, ⟨192, 72, 2⟩, ⟨192, 78, 2⟩,
    ⟨192, 84, 1⟩, ⟨192, 108, 1⟩, ⟨192, 114, 3⟩, ⟨192, 120, 5⟩,
    ⟨192, 126, 3⟩, ⟨192, 132, 1⟩, ⟨192, 150, 2⟩, ⟨192, 156, 5⟩,
    ⟨192, 162, 5⟩, ⟨192, 168, 2⟩, ⟨192, 186, 2⟩, ⟨192, 192, 3⟩,
    ⟨192, 198, 2⟩, ⟨192, 216, 1⟩, ⟨192, 222, 1⟩, ⟨198, 72, 1⟩,
    ⟨198, 78, 1⟩, ⟨198, 114, 2⟩, ⟨198, 120, 3⟩, ⟨198, 126, 2⟩,
    ⟨198, 150, 1⟩, ⟨198, 156, 3⟩, ⟨198, 162, 3⟩, ⟨198, 168, 1⟩,
    ⟨198, 186, 1⟩, ⟨198, 192, 2⟩, ⟨198, 198, 1⟩, ⟨216, 114, 1⟩,
    ⟨216, 120, 1⟩, ⟨216, 126, 1⟩, ⟨216, 156, 1⟩, ⟨216, 162, 1⟩,
    ⟨216, 192, 1⟩, ⟨222, 114, 1⟩, ⟨222, 120, 1⟩, ⟨222, 126, 1⟩,
    ⟨222, 156, 1⟩, ⟨222, 162, 1⟩, ⟨222, 192, 1⟩, ⟨1, 67, 1⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 128 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  rfl

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk1
