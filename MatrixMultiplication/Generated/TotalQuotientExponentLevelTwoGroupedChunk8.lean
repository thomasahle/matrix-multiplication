import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk8

/-!
# Total-quotient grouped level-two proof chunk 8

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk8

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨256704, 67, 0⟩,
    ⟨772584564, 82, 1⟩,
    ⟨210552, 174, 0⟩,
    ⟨1752048, 178, 1⟩,
    ⟨365999952, 82, 0⟩,
    ⟨20277622976, 68, 1⟩,
    ⟨1906528, 194, 0⟩,
    ⟨101444548, 170, 1⟩,
    ⟨102790504, 79, 0⟩,
    ⟨7306304152, 41, 1⟩,
    ⟨2034852, 216, 0⟩,
    ⟨1494090356, 66, 0⟩,
    ⟨168120645488, 78, 1⟩,
    ⟨1906528, 173, 0⟩,
    ⟨48139832, 177, 1⟩,
    ⟨234336, 195, 0⟩,
    ⟨670176, 171, 1⟩,
    ⟨34560, 218, 0⟩,
    ⟨195696, 203, 2⟩,
    ⟨8421012, 100, 2⟩,
    ⟨276432, 217, 0⟩,
    ⟨272400, 224, 2⟩,
    ⟨51304440, 67, 2⟩,
    ⟨122964, 213, 2⟩,
    ⟨164477928, 63, 2⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 8.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk8.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk8.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk8
