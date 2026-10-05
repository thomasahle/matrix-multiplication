import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk13

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (38, 17), (38, 18), (38, 19), (38, 20), (38, 21), (38, 22),
    (38, 24), (38, 25), (38, 26), (38, 27), (38, 28), (38, 30),
    (38, 31), (38, 32), (38, 33), (38, 35), (38, 36), (38, 37),
    (38, 39), (38, 40), (38, 42), (39, 1), (39, 2), (39, 3),
    (39, 4), (39, 5), (39, 6), (39, 7), (39, 8), (39, 10),
    (39, 11), (39, 12), (39, 13), (39, 14), (39, 15), (39, 16),
    (39, 18), (39, 19), (39, 20), (39, 21), (39, 22), (39, 23),
    (39, 25), (39, 26), (39, 27), (39, 28), (39, 29), (39, 31),
    (39, 32), (39, 33), (39, 34), (39, 36), (39, 37), (39, 38),
    (39, 40), (39, 41), (39, 43), (40, 0), (40, 1), (40, 2),
    (40, 3), (40, 4), (40, 5), (40, 6), (40, 7), (40, 8),
    (40, 9), (40, 10), (40, 11), (40, 12), (40, 13), (40, 14),
    (40, 15), (40, 16), (40, 17), (40, 18), (40, 19), (40, 20),
    (40, 21), (40, 22), (40, 23), (40, 24), (40, 25), (40, 26),
    (40, 27), (40, 28), (40, 29), (40, 30), (40, 31), (40, 32),
    (40, 33), (40, 34), (40, 35), (40, 36), (40, 37), (40, 38),
    (40, 39), (40, 40), (40, 41), (40, 42), (40, 43), (40, 44),
    (41, 0), (41, 1), (41, 2), (41, 3), (41, 4), (41, 5),
    (41, 6), (41, 7), (41, 9), (41, 10), (41, 11), (41, 12),
    (41, 13), (41, 14), (41, 15), (41, 17), (41, 18)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 1547 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk13
