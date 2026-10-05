import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk14

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (41, 19), (41, 20), (41, 21), (41, 22), (41, 24), (41, 25),
    (41, 26), (41, 27), (41, 28), (41, 30), (41, 31), (41, 32),
    (41, 33), (41, 35), (41, 36), (41, 37), (41, 39), (41, 40),
    (41, 42), (42, 1), (42, 2), (42, 3), (42, 4), (42, 5),
    (42, 6), (42, 7), (42, 8), (42, 10), (42, 11), (42, 12),
    (42, 13), (42, 14), (42, 15), (42, 16), (42, 18), (42, 19),
    (42, 20), (42, 21), (42, 22), (42, 23), (42, 25), (42, 26),
    (42, 27), (42, 28), (42, 29), (42, 31), (42, 32), (42, 33),
    (42, 34), (42, 36), (42, 37), (42, 38), (42, 40), (42, 41),
    (42, 43), (43, 0), (43, 1), (43, 2), (43, 3), (43, 4),
    (43, 5), (43, 6), (43, 7), (43, 9), (43, 10), (43, 11),
    (43, 12), (43, 13), (43, 14), (43, 15), (43, 17), (43, 18),
    (43, 19), (43, 20), (43, 21), (43, 22), (43, 24), (43, 25),
    (43, 26), (43, 27), (43, 28), (43, 30), (43, 31), (43, 32),
    (43, 33), (43, 35), (43, 36), (43, 37), (43, 39), (43, 40),
    (43, 42), (44, 1), (44, 2), (44, 3), (44, 4), (44, 5),
    (44, 6), (44, 7), (44, 10), (44, 11), (44, 12), (44, 13),
    (44, 14), (44, 15), (44, 18), (44, 19), (44, 20), (44, 21),
    (44, 22), (44, 25), (44, 26), (44, 27), (44, 28), (44, 31),
    (44, 32), (44, 33), (44, 36), (44, 37), (44, 40)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 1666 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk14
