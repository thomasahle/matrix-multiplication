import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk2

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (6, 39), (6, 40), (6, 41), (6, 42), (6, 43), (6, 44),
    (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14),
    (7, 15), (7, 16), (7, 17), (7, 18), (7, 19), (7, 20),
    (7, 21), (7, 22), (7, 23), (7, 24), (7, 25), (7, 26),
    (7, 27), (7, 28), (7, 29), (7, 30), (7, 31), (7, 32),
    (7, 33), (7, 34), (7, 35), (7, 36), (7, 37), (7, 38),
    (7, 39), (7, 40), (7, 41), (7, 42), (7, 43), (7, 44),
    (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14),
    (8, 15), (8, 17), (8, 18), (8, 19), (8, 20), (8, 21),
    (8, 22), (8, 24), (8, 25), (8, 26), (8, 27), (8, 28),
    (8, 30), (8, 31), (8, 32), (8, 33), (8, 35), (8, 36),
    (8, 37), (8, 39), (8, 40), (8, 42), (9, 1), (9, 2),
    (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8),
    (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 15),
    (9, 16), (9, 18), (9, 19), (9, 20), (9, 21), (9, 22),
    (9, 23), (9, 25), (9, 26), (9, 27), (9, 28), (9, 29),
    (9, 31), (9, 32), (9, 33), (9, 34), (9, 36), (9, 37),
    (9, 38), (9, 40), (9, 41), (9, 43), (10, 0), (10, 1),
    (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7),
    (10, 8), (10, 9), (10, 10), (10, 11), (10, 12)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 238 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk2
