import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk5

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (15, 26), (15, 27), (15, 28), (15, 29), (15, 30), (15, 31),
    (15, 32), (15, 33), (15, 34), (15, 35), (15, 36), (15, 37),
    (15, 38), (15, 39), (15, 40), (15, 41), (15, 42), (15, 43),
    (15, 44), (16, 0), (16, 1), (16, 2), (16, 3), (16, 4),
    (16, 5), (16, 6), (16, 7), (16, 9), (16, 10), (16, 11),
    (16, 12), (16, 13), (16, 14), (16, 15), (16, 17), (16, 18),
    (16, 19), (16, 20), (16, 21), (16, 22), (16, 24), (16, 25),
    (16, 26), (16, 27), (16, 28), (16, 30), (16, 31), (16, 32),
    (16, 33), (16, 35), (16, 36), (16, 37), (16, 39), (16, 40),
    (16, 42), (17, 1), (17, 2), (17, 3), (17, 4), (17, 5),
    (17, 6), (17, 7), (17, 8), (17, 10), (17, 11), (17, 12),
    (17, 13), (17, 14), (17, 15), (17, 16), (17, 18), (17, 19),
    (17, 20), (17, 21), (17, 22), (17, 23), (17, 25), (17, 26),
    (17, 27), (17, 28), (17, 29), (17, 31), (17, 32), (17, 33),
    (17, 34), (17, 36), (17, 37), (17, 38), (17, 40), (17, 41),
    (17, 43), (18, 0), (18, 1), (18, 2), (18, 3), (18, 4),
    (18, 5), (18, 6), (18, 7), (18, 8), (18, 9), (18, 10),
    (18, 11), (18, 12), (18, 13), (18, 14), (18, 15), (18, 16),
    (18, 17), (18, 18), (18, 19), (18, 20), (18, 21), (18, 22),
    (18, 23), (18, 24), (18, 25), (18, 26), (18, 27)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 595 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk5
