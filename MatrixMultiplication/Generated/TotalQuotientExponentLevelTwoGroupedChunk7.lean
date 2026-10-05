import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk7

/-!
# Total-quotient grouped level-two proof chunk 7

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk7

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨211230228, 79, 0⟩,
    ⟨2601264184, 41, 1⟩,
    ⟨206871128, 100, 2⟩,
    ⟨194411902080, 81, 0⟩,
    ⟨2557088312064, 62, 1⟩,
    ⟨177046011732, 67, 2⟩,
    ⟨857334, 195, 0⟩,
    ⟨10129854, 170, 1⟩,
    ⟨1184736, 203, 2⟩,
    ⟨426732, 217, 0⟩,
    ⟨789222, 224, 2⟩,
    ⟨112512596, 66, 0⟩,
    ⟨2430703656, 82, 1⟩,
    ⟨442986, 173, 0⟩,
    ⟨1110948, 177, 1⟩,
    ⟨767808, 213, 2⟩,
    ⟨25684846, 82, 0⟩,
    ⟨52142660, 68, 1⟩,
    ⟨51123560, 63, 2⟩,
    ⟨635712, 171, 1⟩,
    ⟨421354248, 67, 0⟩,
    ⟨637260, 178, 1⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 7.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk7.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk7.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk7
