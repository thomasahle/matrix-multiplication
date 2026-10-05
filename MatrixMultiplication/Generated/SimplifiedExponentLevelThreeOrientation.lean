import MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence

/-! Repeated `(X,Z,Y)` regional orientation used by certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

/-! **PROVENANCE QUARANTINE — R7, 2026-08-28 (eab2c7 retained side).**  The retained exponent
`8.200434` this payload feeds is computed from the **ARCHIVED (uncorrected)** evaluator
complement table.  Under the corrected table the same certificate yields `8.160594`, which is
below the `8.2` floor, so the payload was **refuted for endpoint use on 2026-08-28** (commit
`8a8e110`'s analysis).  Every declaration below stays kernel-true *as a statement about the
emitted arrays*; none of it may instantiate an `hsemantic` obligation or any retained-exponent
endpoint.  Listed in `scripts/artifact_provenance_quarantine.txt` and enforced by
`scripts/check_artifact_provenance.sh`.
-/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelThreeOrientation

open MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence

/-- All six labelled regions use the same physical order `(0,2,1)`; repetition is intentional. -/
def order (_region : ℕ) : CoordinateOrder := ⟨0, 2, 1⟩

/-- Every repeated regional order is nevertheless an individual permutation of the coordinates. -/
theorem order_isPermutation (region : ℕ) : (order region).IsPermutation := by
  simp [order, CoordinateOrder.IsPermutation]

end MatrixMultiplication.Generated.SimplifiedExponentLevelThreeOrientation
