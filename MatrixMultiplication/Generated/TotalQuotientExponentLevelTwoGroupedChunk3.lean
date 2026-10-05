import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk3

/-!
# Total-quotient grouped level-two proof chunk 3

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk3

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨672636696, 170, 1⟩,
    ⟨59385816, 41, 1⟩,
    ⟨520713888, 81, 1⟩,
    ⟨30716808, 177, 1⟩,
    ⟨280852728, 68, 1⟩,
    ⟨603720, 171, 1⟩,
    ⟨2732808, 203, 2⟩,
    ⟨1934112, 100, 2⟩,
    ⟨2051424, 224, 2⟩,
    ⟨2845668, 67, 2⟩,
    ⟨177144, 178, 1⟩,
    ⟨99492, 213, 2⟩,
    ⟨5552040, 63, 2⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 3.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk3.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk3.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk3
