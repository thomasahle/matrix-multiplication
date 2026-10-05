import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk10

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (29, 31), (29, 32), (29, 33), (29, 35), (29, 36), (29, 37),
    (29, 39), (29, 40), (29, 42), (30, 1), (30, 2), (30, 3),
    (30, 4), (30, 5), (30, 6), (30, 7), (30, 8), (30, 10),
    (30, 11), (30, 12), (30, 13), (30, 14), (30, 15), (30, 16),
    (30, 18), (30, 19), (30, 20), (30, 21), (30, 22), (30, 23),
    (30, 25), (30, 26), (30, 27), (30, 28), (30, 29), (30, 31),
    (30, 32), (30, 33), (30, 34), (30, 36), (30, 37), (30, 38),
    (30, 40), (30, 41), (30, 43), (31, 0), (31, 1), (31, 2),
    (31, 3), (31, 4), (31, 5), (31, 6), (31, 7), (31, 8),
    (31, 9), (31, 10), (31, 11), (31, 12), (31, 13), (31, 14),
    (31, 15), (31, 16), (31, 17), (31, 18), (31, 19), (31, 20),
    (31, 21), (31, 22), (31, 23), (31, 24), (31, 25), (31, 26),
    (31, 27), (31, 28), (31, 29), (31, 30), (31, 31), (31, 32),
    (31, 33), (31, 34), (31, 35), (31, 36), (31, 37), (31, 38),
    (31, 39), (31, 40), (31, 41), (31, 42), (31, 43), (31, 44),
    (32, 0), (32, 1), (32, 2), (32, 3), (32, 4), (32, 5),
    (32, 6), (32, 7), (32, 8), (32, 9), (32, 10), (32, 11),
    (32, 12), (32, 13), (32, 14), (32, 15), (32, 16), (32, 17),
    (32, 18), (32, 19), (32, 20), (32, 21), (32, 22), (32, 23),
    (32, 24), (32, 25), (32, 26), (32, 27), (32, 28)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 1190 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk10
