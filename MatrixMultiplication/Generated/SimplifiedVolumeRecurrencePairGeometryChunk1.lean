import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk1

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (3, 28), (3, 29), (3, 30), (3, 31), (3, 32), (3, 33),
    (3, 34), (3, 35), (3, 36), (3, 37), (3, 38), (3, 39),
    (3, 40), (3, 41), (3, 42), (3, 43), (3, 44), (4, 9),
    (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15),
    (4, 16), (4, 17), (4, 18), (4, 19), (4, 20), (4, 21),
    (4, 22), (4, 23), (4, 24), (4, 25), (4, 26), (4, 27),
    (4, 28), (4, 29), (4, 30), (4, 31), (4, 32), (4, 33),
    (4, 34), (4, 35), (4, 36), (4, 37), (4, 38), (4, 39),
    (4, 40), (4, 41), (4, 42), (4, 43), (4, 44), (5, 9),
    (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15),
    (5, 16), (5, 17), (5, 18), (5, 19), (5, 20), (5, 21),
    (5, 22), (5, 23), (5, 24), (5, 25), (5, 26), (5, 27),
    (5, 28), (5, 29), (5, 30), (5, 31), (5, 32), (5, 33),
    (5, 34), (5, 35), (5, 36), (5, 37), (5, 38), (5, 39),
    (5, 40), (5, 41), (5, 42), (5, 43), (5, 44), (6, 9),
    (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15),
    (6, 16), (6, 17), (6, 18), (6, 19), (6, 20), (6, 21),
    (6, 22), (6, 23), (6, 24), (6, 25), (6, 26), (6, 27),
    (6, 28), (6, 29), (6, 30), (6, 31), (6, 32), (6, 33),
    (6, 34), (6, 35), (6, 36), (6, 37), (6, 38)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 119 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk1
