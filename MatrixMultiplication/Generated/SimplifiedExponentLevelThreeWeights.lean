import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeWeightsRegion0
import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeWeightsRegion1
import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeWeightsRegion2
import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeWeightsRegion3
import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeWeightsRegion4
import MatrixMultiplication.Generated.SimplifiedExponentLevelThreeWeightsRegion5

/-! Exact level-three positive-integer dual witness; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

/-! **PROVENANCE QUARANTINE — R7, 2026-08-28 (eab2c7 retained side).**  The retained exponent
`8.200434` this payload feeds is computed from the **ARCHIVED (uncorrected)** evaluator
complement table.  Under the corrected table the same certificate yields `8.160594`, which is
below the `8.2` floor, so the payload was **refuted for endpoint use on 2026-08-28** (commit
`8a8e110`'s analysis).  Every declaration below stays kernel-true *as a statement about the
emitted arrays*; none of it may instantiate an `hsemantic` obligation or any retained-exponent
endpoint.  Listed in `scripts/artifact_provenance_quarantine.txt` and enforced by
`scripts/check_artifact_provenance.sh`.
-/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelThreeWeights

open MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence

/-- Region-indexed witness.  Out-of-range regions receive the harmless all-one product family. -/
def dualWeights : ℕ → ℕ → DualWeights
  | 0 => Region0.dualWeights
  | 1 => Region1.dualWeights
  | 2 => Region2.dualWeights
  | 3 => Region3.dualWeights
  | 4 => Region4.dualWeights
  | 5 => Region5.dualWeights
  | _ => fun _ ↦ { x := fun _ ↦ 1, y := fun _ ↦ 1, z := fun _ ↦ 1 }

end MatrixMultiplication.Generated.SimplifiedExponentLevelThreeWeights
