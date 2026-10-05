import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk8

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (24, 6), (24, 7), (24, 8), (24, 10), (24, 11), (24, 12),
    (24, 13), (24, 14), (24, 15), (24, 16), (24, 18), (24, 19),
    (24, 20), (24, 21), (24, 22), (24, 23), (24, 25), (24, 26),
    (24, 27), (24, 28), (24, 29), (24, 31), (24, 32), (24, 33),
    (24, 34), (24, 36), (24, 37), (24, 38), (24, 40), (24, 41),
    (24, 43), (25, 0), (25, 1), (25, 2), (25, 3), (25, 4),
    (25, 5), (25, 6), (25, 7), (25, 8), (25, 9), (25, 10),
    (25, 11), (25, 12), (25, 13), (25, 14), (25, 15), (25, 16),
    (25, 17), (25, 18), (25, 19), (25, 20), (25, 21), (25, 22),
    (25, 23), (25, 24), (25, 25), (25, 26), (25, 27), (25, 28),
    (25, 29), (25, 30), (25, 31), (25, 32), (25, 33), (25, 34),
    (25, 35), (25, 36), (25, 37), (25, 38), (25, 39), (25, 40),
    (25, 41), (25, 42), (25, 43), (25, 44), (26, 0), (26, 1),
    (26, 2), (26, 3), (26, 4), (26, 5), (26, 6), (26, 7),
    (26, 8), (26, 9), (26, 10), (26, 11), (26, 12), (26, 13),
    (26, 14), (26, 15), (26, 16), (26, 17), (26, 18), (26, 19),
    (26, 20), (26, 21), (26, 22), (26, 23), (26, 24), (26, 25),
    (26, 26), (26, 27), (26, 28), (26, 29), (26, 30), (26, 31),
    (26, 32), (26, 33), (26, 34), (26, 35), (26, 36), (26, 37),
    (26, 38), (26, 39), (26, 40), (26, 41), (26, 42)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 952 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk8
