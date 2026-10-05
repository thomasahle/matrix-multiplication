import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatter

/-! Generated exact top-pair scatter check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Mass3Chunk5

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedNumerators : List ℕ := [
    42, 92518, 0, 0, 84, 30, 136, 259515,
    0, 0, 208, 90, 134, 267342, 0, 0,
    210, 86, 42, 93617, 0, 0, 84, 30,
    0, 8797, 0, 0, 0, 0
  ]

opaque recurrence_eq :
    levelThreeMassNumeratorRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 150 30 =
      expectedNumerators := by
  unfold levelThreeMassNumeratorRangeWithPairs
  rw [TopScatter.recurrence_eq]
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Mass3Chunk5
