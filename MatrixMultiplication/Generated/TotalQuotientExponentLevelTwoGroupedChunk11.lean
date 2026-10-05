import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk11

/-!
# Total-quotient grouped level-two proof chunk 11

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk11

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨4113464420, 79, 0⟩,
    ⟨4111536620, 41, 1⟩,
    ⟨1895402320, 100, 2⟩,
    ⟨2702481904980, 75, 0⟩,
    ⟨2702481904980, 58, 1⟩,
    ⟨1383788325860, 78, 2⟩,
    ⟨1840270, 194, 0⟩,
    ⟨1235920, 171, 1⟩,
    ⟨1474030, 203, 2⟩,
    ⟨1129320, 217, 0⟩,
    ⟨923220, 170, 1⟩,
    ⟨753560, 224, 2⟩,
    ⟨1336631100, 66, 0⟩,
    ⟨1652519400, 82, 1⟩,
    ⟨1259656860, 67, 2⟩,
    ⟨1139780, 173, 0⟩,
    ⟨906680, 178, 1⟩,
    ⟨774660, 213, 2⟩,
    ⟨463664400, 82, 0⟩,
    ⟨305620800, 68, 1⟩,
    ⟨394883800, 63, 2⟩,
    ⟨608975640, 67, 0⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 11.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk11.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk11.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk11
