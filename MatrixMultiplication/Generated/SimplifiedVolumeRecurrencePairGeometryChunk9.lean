import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk9

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (26, 43), (26, 44), (27, 0), (27, 1), (27, 2), (27, 3),
    (27, 4), (27, 5), (27, 6), (27, 7), (27, 8), (27, 9),
    (27, 10), (27, 11), (27, 12), (27, 13), (27, 14), (27, 15),
    (27, 16), (27, 17), (27, 18), (27, 19), (27, 20), (27, 21),
    (27, 22), (27, 23), (27, 24), (27, 25), (27, 26), (27, 27),
    (27, 28), (27, 29), (27, 30), (27, 31), (27, 32), (27, 33),
    (27, 34), (27, 35), (27, 36), (27, 37), (27, 38), (27, 39),
    (27, 40), (27, 41), (27, 42), (27, 43), (27, 44), (28, 0),
    (28, 1), (28, 2), (28, 3), (28, 4), (28, 5), (28, 6),
    (28, 7), (28, 8), (28, 9), (28, 10), (28, 11), (28, 12),
    (28, 13), (28, 14), (28, 15), (28, 16), (28, 17), (28, 18),
    (28, 19), (28, 20), (28, 21), (28, 22), (28, 23), (28, 24),
    (28, 25), (28, 26), (28, 27), (28, 28), (28, 29), (28, 30),
    (28, 31), (28, 32), (28, 33), (28, 34), (28, 35), (28, 36),
    (28, 37), (28, 38), (28, 39), (28, 40), (28, 41), (28, 42),
    (28, 43), (28, 44), (29, 0), (29, 1), (29, 2), (29, 3),
    (29, 4), (29, 5), (29, 6), (29, 7), (29, 9), (29, 10),
    (29, 11), (29, 12), (29, 13), (29, 14), (29, 15), (29, 17),
    (29, 18), (29, 19), (29, 20), (29, 21), (29, 22), (29, 24),
    (29, 25), (29, 26), (29, 27), (29, 28), (29, 30)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 1071 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk9
