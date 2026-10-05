import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3Chunk0
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3Chunk1
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3Chunk2
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3Chunk3
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3Chunk4
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3Chunk5
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3Chunk6
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3Chunk7
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3Chunk8

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Mass3

open MatrixMultiplication.SimplifiedVolumeReconstruction

def expectedNumerators : Array ℕ :=
  (Mass3Chunk0.expectedNumerators ++
    Mass3Chunk1.expectedNumerators ++
    Mass3Chunk2.expectedNumerators ++
    Mass3Chunk3.expectedNumerators ++
    Mass3Chunk4.expectedNumerators ++
    Mass3Chunk5.expectedNumerators ++
    Mass3Chunk6.expectedNumerators ++
    Mass3Chunk7.expectedNumerators ++
    Mass3Chunk8.expectedNumerators).toArray

theorem recurrence_eq :
    levelThreeMassNumerators generatedPrimaryTables = expectedNumerators := by
  unfold levelThreeMassNumerators
  rw [PairGeometry.recurrence_eq]
  unfold levelThreeMassNumeratorsWithPairs expectedNumerators
  rw [Mass3Chunk0.recurrence_eq, Mass3Chunk1.recurrence_eq, Mass3Chunk2.recurrence_eq, Mass3Chunk3.recurrence_eq, Mass3Chunk4.recurrence_eq, Mass3Chunk5.recurrence_eq, Mass3Chunk6.recurrence_eq, Mass3Chunk7.recurrence_eq, Mass3Chunk8.recurrence_eq]

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Mass3
