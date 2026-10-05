import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedBranchTargets
import MatrixMultiplication.SimplifiedExponentRecurrenceForm
import MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedData

/-!
# Compact level-two branch-2 normalization check

This generated proof leaf normalizes the 67-record sufficient statistic for coordinate branch two
and compares it with the directed-log target form of certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.

The producer is untrusted.  Lean evaluates the exact signed-log form and checks the displayed
target; no sparse primary table or 1,620-record expression is unfolded here.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedBranchCheck2

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRecurrence
open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The compact coordinate-two form normalizes to the certificate's branch-two target. -/
theorem normalized_eq :
    Form.normalize
        (inputBranchForm
          MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedData.expectedInputs 2) =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedBranchTargets.branch2 := by
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedBranchCheck2
