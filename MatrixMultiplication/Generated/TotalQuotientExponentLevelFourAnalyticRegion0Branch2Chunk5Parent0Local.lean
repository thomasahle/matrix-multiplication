import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk5Parent0LocalArithmetic

/-!
# Parent-local beta-four arithmetic for region 0, branch 2, parent 56

This module imports the bounded exact row data for certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` and uses the
generic route-once soundness theorem to recover the original dense scatter semantics.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.DyadicEntropyForm

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- The lightweight checker reconstructs the exact compact pooled row.

Proof sketch: the route certificate is checked once, the imported sparse canonicalization theorem
computes its nonzero sufficient statistic, and `routedScatterOn_eq_scatterOn` transports that result
back to the exact source fold. -/
theorem pooledNumerators_eq_local :
    dropZeros (localData.scatterOn parent coordinate
      (List.range MatrixMultiplication.BetaFourLocalGeometry.parentSupportWidth)) =
        expectedPooledNumerators := by
  rw [← localData.routedScatterOn_eq_scatterOn parent coordinate]
  rw [routedContributions_eq_local]
  exact routedPooledNumerators_eq

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5.Parent0
