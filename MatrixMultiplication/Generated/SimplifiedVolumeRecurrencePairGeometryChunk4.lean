import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk4

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (12, 42), (12, 43), (12, 44), (13, 0), (13, 1), (13, 2),
    (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8),
    (13, 9), (13, 10), (13, 11), (13, 12), (13, 13), (13, 14),
    (13, 15), (13, 16), (13, 17), (13, 18), (13, 19), (13, 20),
    (13, 21), (13, 22), (13, 23), (13, 24), (13, 25), (13, 26),
    (13, 27), (13, 28), (13, 29), (13, 30), (13, 31), (13, 32),
    (13, 33), (13, 34), (13, 35), (13, 36), (13, 37), (13, 38),
    (13, 39), (13, 40), (13, 41), (13, 42), (13, 43), (13, 44),
    (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5),
    (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11),
    (14, 12), (14, 13), (14, 14), (14, 15), (14, 16), (14, 17),
    (14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23),
    (14, 24), (14, 25), (14, 26), (14, 27), (14, 28), (14, 29),
    (14, 30), (14, 31), (14, 32), (14, 33), (14, 34), (14, 35),
    (14, 36), (14, 37), (14, 38), (14, 39), (14, 40), (14, 41),
    (14, 42), (14, 43), (14, 44), (15, 0), (15, 1), (15, 2),
    (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8),
    (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14),
    (15, 15), (15, 16), (15, 17), (15, 18), (15, 19), (15, 20),
    (15, 21), (15, 22), (15, 23), (15, 24), (15, 25)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 476 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk4
