import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk6

/-!
# Total-quotient grouped level-two proof chunk 6

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk6

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨840200, 195, 0⟩,
    ⟨4148160, 170, 1⟩,
    ⟨1818120, 203, 2⟩,
    ⟨1050507075, 79, 0⟩,
    ⟨2087310460, 41, 1⟩,
    ⟨2087310460, 100, 2⟩,
    ⟨995280, 216, 0⟩,
    ⟨3022200, 224, 2⟩,
    ⟨1886185860, 67, 0⟩,
    ⟨3680452000, 82, 1⟩,
    ⟨3680452000, 67, 2⟩,
    ⟨2020200, 173, 0⟩,
    ⟨3368640, 177, 1⟩,
    ⟨4055760, 213, 2⟩,
    ⟨3510416960, 82, 0⟩,
    ⟨6899174160, 68, 1⟩,
    ⟨6899174160, 63, 2⟩,
    ⟨1476527164830, 76, 0⟩,
    ⟨2736871728660, 58, 1⟩,
    ⟨2736871728660, 82, 2⟩,
    ⟨692160, 171, 1⟩,
    ⟨312480, 217, 0⟩,
    ⟨687120, 178, 1⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 6.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk6.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk6.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk6
