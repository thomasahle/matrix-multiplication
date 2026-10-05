import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatter

/-! Generated exact top-pair scatter check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Mass3Chunk6

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedNumerators : List ℕ := [
    6, 23305, 0, 0, 6, 0, 42, 97988,
    0, 0, 84, 30, 84, 160227, 0, 0,
    126, 42, 42, 100173, 0, 0, 84, 30,
    0, 21976, 0, 0, 6, 0
  ]

opaque recurrence_eq :
    levelThreeMassNumeratorRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 180 30 =
      expectedNumerators := by
  unfold levelThreeMassNumeratorRangeWithPairs
  rw [TopScatter.recurrence_eq]
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Mass3Chunk6
