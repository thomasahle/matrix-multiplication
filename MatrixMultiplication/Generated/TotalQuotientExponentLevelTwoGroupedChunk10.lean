import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk10

/-!
# Total-quotient grouped level-two proof chunk 10

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk10

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨1800824, 194, 0⟩,
    ⟨866956, 171, 1⟩,
    ⟨1800824, 203, 2⟩,
    ⟨1671780, 79, 0⟩,
    ⟨83883624, 41, 1⟩,
    ⟨153519196, 100, 2⟩,
    ⟨1082840, 216, 0⟩,
    ⟨900912, 170, 1⟩,
    ⟨1766428, 224, 2⟩,
    ⟨2718892940, 67, 0⟩,
    ⟨1407799520, 82, 1⟩,
    ⟨2718892940, 67, 2⟩,
    ⟨2207336, 173, 0⟩,
    ⟨1011488, 178, 1⟩,
    ⟨2207336, 213, 2⟩,
    ⟨921934616, 82, 0⟩,
    ⟨480425456, 68, 1⟩,
    ⟨921934616, 63, 2⟩,
    ⟨1091695304926, 78, 0⟩,
    ⟨196182820740, 45, 1⟩,
    ⟨406113886398, 77, 2⟩,
    ⟨1621328058584, 75, 0⟩,
    ⟨755072147856, 87, 1⟩,
    ⟨1621328058584, 49, 2⟩,
    ⟨320487431440, 75, 1⟩,
    ⟨685429571112, 55, 2⟩,
    ⟨683588, 217, 0⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 10.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk10.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk10.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk10
