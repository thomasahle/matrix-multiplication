import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk0
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk1
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk2
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk3
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk4
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk5
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk6
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk7
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk8
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk9
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk10
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk11
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk12
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk13
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometryChunk14

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometry

open MatrixMultiplication.SimplifiedVolumeReconstruction

def expectedIndices : Array (ℕ × ℕ) :=
  (PairGeometryChunk0.expectedIndices ++
    PairGeometryChunk1.expectedIndices ++
    PairGeometryChunk2.expectedIndices ++
    PairGeometryChunk3.expectedIndices ++
    PairGeometryChunk4.expectedIndices ++
    PairGeometryChunk5.expectedIndices ++
    PairGeometryChunk6.expectedIndices ++
    PairGeometryChunk7.expectedIndices ++
    PairGeometryChunk8.expectedIndices ++
    PairGeometryChunk9.expectedIndices ++
    PairGeometryChunk10.expectedIndices ++
    PairGeometryChunk11.expectedIndices ++
    PairGeometryChunk12.expectedIndices ++
    PairGeometryChunk13.expectedIndices ++
    PairGeometryChunk14.expectedIndices).toArray

theorem recurrence_eq : computedPairShapeIndices = expectedIndices := by
  unfold computedPairShapeIndices expectedIndices
  rw [PairGeometryChunk0.recurrence_eq, PairGeometryChunk1.recurrence_eq, PairGeometryChunk2.recurrence_eq, PairGeometryChunk3.recurrence_eq, PairGeometryChunk4.recurrence_eq, PairGeometryChunk5.recurrence_eq, PairGeometryChunk6.recurrence_eq, PairGeometryChunk7.recurrence_eq, PairGeometryChunk8.recurrence_eq, PairGeometryChunk9.recurrence_eq, PairGeometryChunk10.recurrence_eq, PairGeometryChunk11.recurrence_eq, PairGeometryChunk12.recurrence_eq, PairGeometryChunk13.recurrence_eq, PairGeometryChunk14.recurrence_eq]

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometry
