import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk9

/-!
# Total-quotient grouped level-two proof chunk 9

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk9

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨532596, 195, 0⟩,
    ⟨297908630, 203, 2⟩,
    ⟨6784296, 79, 0⟩,
    ⟨1299300504, 100, 2⟩,
    ⟨881790, 217, 0⟩,
    ⟨298040294, 224, 2⟩,
    ⟨98082182, 67, 0⟩,
    ⟨575707056, 67, 2⟩,
    ⟨660234, 173, 0⟩,
    ⟨293188292, 213, 2⟩,
    ⟨97111674, 82, 0⟩,
    ⟨627019218, 63, 2⟩,
    ⟨1008672, 194, 0⟩,
    ⟨10927790456, 78, 0⟩,
    ⟨49261720, 193, 0⟩,
    ⟨73850113000, 93, 2⟩,
    ⟨46204096, 215, 0⟩,
    ⟨49261720, 171, 0⟩,
    ⟨188610895384, 81, 0⟩,
    ⟨1110781120912, 42, 2⟩,
    ⟨769692, 171, 1⟩,
    ⟨156631812, 41, 1⟩,
    ⟨84888, 218, 0⟩,
    ⟨899316, 170, 1⟩,
    ⟨238950, 82, 1⟩,
    ⟨19008, 174, 0⟩,
    ⟨177342, 178, 1⟩,
    ⟨25547820, 68, 1⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 9.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk9.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk9.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk9
