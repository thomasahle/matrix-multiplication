import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeWeightsRegion0
import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoMassThreeData

/-! Exact active level-three nodes for region 0; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

/-! **PROVENANCE QUARANTINE — R7, 2026-08-28 (eab2c7 retained side).**  The retained exponent
`8.200434` this payload feeds is computed from the **ARCHIVED (uncorrected)** evaluator
complement table.  Under the corrected table the same certificate yields `8.160594`, which is
below the `8.2` floor, so the payload was **refuted for endpoint use on 2026-08-28** (commit
`8a8e110`'s analysis).  Every declaration below stays kernel-true *as a statement about the
emitted arrays*; none of it may instantiate an `hsemantic` obligation or any retained-exponent
endpoint.  Listed in `scripts/artifact_provenance_quarantine.txt` and enforced by
`scripts/check_artifact_provenance.sh`.
-/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelThreeActiveNodes.Region0

open MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Certificate-order list of nodes with positive outer occurrence mass in this region. -/
def expectedActiveNodes : List ℕ := [1, 6, 7, 10, 11, 12, 13, 16, 17, 18, 19, 22, 23, 24, 25, 28, 29, 31, 36, 37, 40, 41, 42, 43, 46, 47, 48, 49, 52, 53, 54, 55, 58, 59, 60, 61, 64, 65, 66, 67, 70, 71, 72, 73, 76, 77, 78, 82, 83, 84, 85, 88, 89, 90, 91, 94, 95, 96, 97, 100, 101, 102, 103, 106, 107, 108, 109, 112, 113, 114, 115, 118, 119, 121]

/-- The serialized dual rows cover exactly the positive occurrence-mass nodes in this region. -/
opaque activeNodes_eq :
    activeNodes generatedPrimaryTables MassThree.expectedNumerators 0 =
      expectedActiveNodes := by
  unfold activeNodes outerNumerator generatedPrimaryTables pos3AChunks
  rw [Pos3AData0.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedExponentLevelThreeActiveNodes.Region0
