import MatrixMultiplication.SimplifiedExponentRootRecurrence
import MatrixMultiplication.SignedDyadicLogCanonical

/-! Exact root retained-rate recurrence data; certificate SHA-256 `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

/-! **PROVENANCE QUARANTINE — R7, 2026-08-28 (eab2c7 retained side).**  The retained exponent
`8.200434` this payload feeds is computed from the **ARCHIVED (uncorrected)** evaluator
complement table.  Under the corrected table the same certificate yields `8.160594`, which is
below the `8.2` floor, so the payload was **refuted for endpoint use on 2026-08-28** (commit
`8a8e110`'s analysis).  Every declaration below stays kernel-true *as a statement about the
emitted arrays*; none of it may instantiate an `hsemantic` obligation or any retained-exponent
endpoint.  Listed in `scripts/artifact_provenance_quarantine.txt` and enforced by
`scripts/check_artifact_provenance.sh`.
-/

namespace MatrixMultiplication.Generated.SimplifiedExponentRoot.Root2Y

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRootRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def rows : CompatibilityRows :=
  { pooled := []
    first := []
    groups := [] }

def expectedForm : Form := { constantNumerator := 0, terms := [] }

theorem recurrence_normalize :
    Form.fastCanonical (rows.form 116) = expectedForm := by
  decide

end MatrixMultiplication.Generated.SimplifiedExponentRoot.Root2Y
