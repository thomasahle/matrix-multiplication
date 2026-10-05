import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk6

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (18, 28), (18, 29), (18, 30), (18, 31), (18, 32), (18, 33),
    (18, 34), (18, 35), (18, 36), (18, 37), (18, 38), (18, 39),
    (18, 40), (18, 41), (18, 42), (18, 43), (18, 44), (19, 0),
    (19, 1), (19, 2), (19, 3), (19, 4), (19, 5), (19, 6),
    (19, 7), (19, 8), (19, 9), (19, 10), (19, 11), (19, 12),
    (19, 13), (19, 14), (19, 15), (19, 16), (19, 17), (19, 18),
    (19, 19), (19, 20), (19, 21), (19, 22), (19, 23), (19, 24),
    (19, 25), (19, 26), (19, 27), (19, 28), (19, 29), (19, 30),
    (19, 31), (19, 32), (19, 33), (19, 34), (19, 35), (19, 36),
    (19, 37), (19, 38), (19, 39), (19, 40), (19, 41), (19, 42),
    (19, 43), (19, 44), (20, 0), (20, 1), (20, 2), (20, 3),
    (20, 4), (20, 5), (20, 6), (20, 7), (20, 8), (20, 9),
    (20, 10), (20, 11), (20, 12), (20, 13), (20, 14), (20, 15),
    (20, 16), (20, 17), (20, 18), (20, 19), (20, 20), (20, 21),
    (20, 22), (20, 23), (20, 24), (20, 25), (20, 26), (20, 27),
    (20, 28), (20, 29), (20, 30), (20, 31), (20, 32), (20, 33),
    (20, 34), (20, 35), (20, 36), (20, 37), (20, 38), (20, 39),
    (20, 40), (20, 41), (20, 42), (20, 43), (20, 44), (21, 0),
    (21, 1), (21, 2), (21, 3), (21, 4), (21, 5), (21, 6),
    (21, 7), (21, 8), (21, 9), (21, 10), (21, 11)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 714 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk6
