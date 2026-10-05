import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk12

/-!
# Total-quotient grouped level-two proof chunk 12

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk12

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨236290922, 66, 0⟩,
    ⟨1484553516, 82, 1⟩,
    ⟨997158, 173, 0⟩,
    ⟨5486344, 177, 1⟩,
    ⟨3312649674, 82, 0⟩,
    ⟨4009845056, 68, 1⟩,
    ⟨218343508056, 78, 0⟩,
    ⟨1205170539564, 38, 1⟩,
    ⟨52996928, 215, 0⟩,
    ⟨300823264, 170, 1⟩,
    ⟨159600, 195, 0⟩,
    ⟨116590176, 79, 0⟩,
    ⟨162573456, 41, 1⟩,
    ⟨820980, 217, 0⟩,
    ⟨2836578, 67, 0⟩,
    ⟨1889406, 194, 0⟩,
    ⟨873996, 203, 2⟩,
    ⟨46713664, 100, 2⟩,
    ⟨804006, 224, 2⟩,
    ⟨1133952, 67, 2⟩,
    ⟨2886676, 172, 0⟩,
    ⟨1642952, 213, 2⟩,
    ⟨1562978104, 63, 2⟩,
    ⟨1132644, 216, 0⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 12.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk12.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk12.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk12
