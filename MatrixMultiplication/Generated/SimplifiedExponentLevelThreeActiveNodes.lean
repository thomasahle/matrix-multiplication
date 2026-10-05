import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeActiveNodesRegion0
import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeActiveNodesRegion1
import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeActiveNodesRegion2
import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeActiveNodesRegion3
import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeActiveNodesRegion4
import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeActiveNodesRegion5

/-! Exact active-node boundary for the level-three recurrence; certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

/-! **PROVENANCE QUARANTINE — R7, 2026-08-28 (eab2c7 retained side).**  The retained exponent
`8.200434` this payload feeds is computed from the **ARCHIVED (uncorrected)** evaluator
complement table.  Under the corrected table the same certificate yields `8.160594`, which is
below the `8.2` floor, so the payload was **refuted for endpoint use on 2026-08-28** (commit
`8a8e110`'s analysis).  Every declaration below stays kernel-true *as a statement about the
emitted arrays*; none of it may instantiate an `hsemantic` obligation or any retained-exponent
endpoint.  Listed in `scripts/artifact_provenance_quarantine.txt` and enforced by
`scripts/check_artifact_provenance.sh`.
-/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelThreeActiveNodes

/-- Region-indexed active-node lists; out-of-range regions are empty. -/
def expectedActiveNodes : ℕ → List ℕ
  | 0 => Region0.expectedActiveNodes
  | 1 => Region1.expectedActiveNodes
  | 2 => Region2.expectedActiveNodes
  | 3 => Region3.expectedActiveNodes
  | 4 => Region4.expectedActiveNodes
  | 5 => Region5.expectedActiveNodes
  | _ => []

end MatrixMultiplication.Generated.SimplifiedExponentLevelThreeActiveNodes
