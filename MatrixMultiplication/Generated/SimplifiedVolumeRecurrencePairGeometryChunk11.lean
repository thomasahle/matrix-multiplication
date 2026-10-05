import MatrixMultiplication.SimplifiedVolumeReconstruction

/-! Exact static ordered-pair child-index table. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk11

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedIndices : List (ℕ × ℕ) := [
    (32, 29), (32, 30), (32, 31), (32, 32), (32, 33), (32, 34),
    (32, 35), (32, 36), (32, 37), (32, 38), (32, 39), (32, 40),
    (32, 41), (32, 42), (32, 43), (32, 44), (33, 0), (33, 1),
    (33, 2), (33, 3), (33, 4), (33, 5), (33, 6), (33, 7),
    (33, 8), (33, 9), (33, 10), (33, 11), (33, 12), (33, 13),
    (33, 14), (33, 15), (33, 16), (33, 17), (33, 18), (33, 19),
    (33, 20), (33, 21), (33, 22), (33, 23), (33, 24), (33, 25),
    (33, 26), (33, 27), (33, 28), (33, 29), (33, 30), (33, 31),
    (33, 32), (33, 33), (33, 34), (33, 35), (33, 36), (33, 37),
    (33, 38), (33, 39), (33, 40), (33, 41), (33, 42), (33, 43),
    (33, 44), (34, 0), (34, 1), (34, 2), (34, 3), (34, 4),
    (34, 5), (34, 6), (34, 7), (34, 9), (34, 10), (34, 11),
    (34, 12), (34, 13), (34, 14), (34, 15), (34, 17), (34, 18),
    (34, 19), (34, 20), (34, 21), (34, 22), (34, 24), (34, 25),
    (34, 26), (34, 27), (34, 28), (34, 30), (34, 31), (34, 32),
    (34, 33), (34, 35), (34, 36), (34, 37), (34, 39), (34, 40),
    (34, 42), (35, 1), (35, 2), (35, 3), (35, 4), (35, 5),
    (35, 6), (35, 7), (35, 8), (35, 10), (35, 11), (35, 12),
    (35, 13), (35, 14), (35, 15), (35, 16), (35, 18), (35, 19),
    (35, 20), (35, 21), (35, 22), (35, 23), (35, 25)
  ]

opaque recurrence_eq :
    computedPairShapeIndexRange 1309 119 = expectedIndices := by
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.PairGeometryChunk11
