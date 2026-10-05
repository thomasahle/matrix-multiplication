import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk8
import MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdgeData
import MatrixMultiplication.TotalQuotientExponentLevelTwoInputData

/-!
# Lightweight total-quotient level-two input check, chunk 8, part 0

This proof leaf reconstructs 45 exact recurrence inputs from only the three sparse families used at
level two.  The result is compared with one half of the definition-only literal consumed by the
compact grouping checker.  The producer is untrusted; Lean evaluates the finite equality.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk8Part0

open MatrixMultiplication.SimplifiedExponentLevelTwoInput

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 10000000
set_option Elab.async false

/-- This 45-row sparse-table range equals part 0 of emitted input chunk 8. -/
theorem inputs_eq :
    edgeInputRangeWithMassThree
        MatrixMultiplication.TotalQuotientExponentLevelTwoInputData.tables
        MatrixMultiplication.TotalQuotientExponentLevelTwoInputData.massThree
        MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdgeData.expectedActiveEdges.toList
        720 45 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk8.expectedInputs.take 45 := by
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk8Part0
