import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk3

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (10, 13), (10, 14), (10, 15), (10, 16), (10, 17), (10, 18),
    (10, 19), (10, 20), (10, 21), (10, 22), (10, 23), (10, 24),
    (10, 25), (10, 26), (10, 27), (10, 28), (10, 29), (10, 30),
    (10, 31), (10, 32), (10, 33), (10, 34), (10, 35), (10, 36),
    (10, 37), (10, 38), (10, 39), (10, 40), (10, 41), (10, 42),
    (10, 43), (10, 44), (11, 0), (11, 1), (11, 2), (11, 3),
    (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9),
    (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (11, 15),
    (11, 16), (11, 17), (11, 18), (11, 19), (11, 20), (11, 21),
    (11, 22), (11, 23), (11, 24), (11, 25), (11, 26), (11, 27),
    (11, 28), (11, 29), (11, 30), (11, 31), (11, 32), (11, 33),
    (11, 34), (11, 35), (11, 36), (11, 37), (11, 38), (11, 39),
    (11, 40), (11, 41), (11, 42), (11, 43), (11, 44), (12, 0),
    (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6),
    (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12),
    (12, 13), (12, 14), (12, 15), (12, 16), (12, 17), (12, 18),
    (12, 19), (12, 20), (12, 21), (12, 22), (12, 23), (12, 24),
    (12, 25), (12, 26), (12, 27), (12, 28), (12, 29), (12, 30),
    (12, 31), (12, 32), (12, 33), (12, 34), (12, 35), (12, 36),
    (12, 37), (12, 38), (12, 39), (12, 40), (12, 41)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 357 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk3
