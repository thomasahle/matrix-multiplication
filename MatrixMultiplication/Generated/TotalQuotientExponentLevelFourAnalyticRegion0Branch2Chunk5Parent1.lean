import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk5Parent1Raw

/-! Canonical compatibility sufficient statistic for level-four region 0, branch 2,
chunk 5, parent 57; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The imported raw stage has
already discarded the dense row reconstruction, so this module normalizes only a small literal
signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5.Parent1

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Raw form after extracting powers of two from every logarithm argument. -/
def expectedPower : Form := Form.normalizePowersOfTwo expectedRaw

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := Form.structuralFastCanonical expectedPower

/-- The staged checks compose to the original structural canonicalization statement. -/
theorem recurrence_structuralPowerCanonical :
    Form.structuralPowerCanonical
      (branchFormOnParentsFrom Top.expectedRows BetaThree.expectedRows
        Orientation.order Weights.Region0.dualWeights 0 [parent] 2) =
      expectedForm := by
  unfold Form.structuralPowerCanonical expectedForm expectedPower
  rw [raw_eq]

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5.Parent1
