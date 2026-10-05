import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatter

/-! Generated exact top-pair scatter check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Mass3Chunk2

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedNumerators : List ℕ := [
    0, 1505, 0, 0, 0, 0, 12, 21001,
    0, 0, 24, 6, 42, 98874, 0, 0,
    84, 30, 42, 99115, 0, 0, 84, 30,
    12, 20293, 0, 0, 24, 6
  ]

opaque recurrence_eq :
    levelThreeMassNumeratorRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 60 30 =
      expectedNumerators := by
  unfold levelThreeMassNumeratorRangeWithPairs
  rw [TopScatter.recurrence_eq]
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Mass3Chunk2
