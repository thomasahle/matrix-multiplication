import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk12

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (35, 26), (35, 27), (35, 28), (35, 29), (35, 31), (35, 32),
    (35, 33), (35, 34), (35, 36), (35, 37), (35, 38), (35, 40),
    (35, 41), (35, 43), (36, 0), (36, 1), (36, 2), (36, 3),
    (36, 4), (36, 5), (36, 6), (36, 7), (36, 8), (36, 9),
    (36, 10), (36, 11), (36, 12), (36, 13), (36, 14), (36, 15),
    (36, 16), (36, 17), (36, 18), (36, 19), (36, 20), (36, 21),
    (36, 22), (36, 23), (36, 24), (36, 25), (36, 26), (36, 27),
    (36, 28), (36, 29), (36, 30), (36, 31), (36, 32), (36, 33),
    (36, 34), (36, 35), (36, 36), (36, 37), (36, 38), (36, 39),
    (36, 40), (36, 41), (36, 42), (36, 43), (36, 44), (37, 0),
    (37, 1), (37, 2), (37, 3), (37, 4), (37, 5), (37, 6),
    (37, 7), (37, 8), (37, 9), (37, 10), (37, 11), (37, 12),
    (37, 13), (37, 14), (37, 15), (37, 16), (37, 17), (37, 18),
    (37, 19), (37, 20), (37, 21), (37, 22), (37, 23), (37, 24),
    (37, 25), (37, 26), (37, 27), (37, 28), (37, 29), (37, 30),
    (37, 31), (37, 32), (37, 33), (37, 34), (37, 35), (37, 36),
    (37, 37), (37, 38), (37, 39), (37, 40), (37, 41), (37, 42),
    (37, 43), (37, 44), (38, 0), (38, 1), (38, 2), (38, 3),
    (38, 4), (38, 5), (38, 6), (38, 7), (38, 9), (38, 10),
    (38, 11), (38, 12), (38, 13), (38, 14), (38, 15)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 1428 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk12
