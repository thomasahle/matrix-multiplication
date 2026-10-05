import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk16

/-!
# Total-quotient grouped level-two proof chunk 16

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk16

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨497366223024, 70, 0⟩,
    ⟨5661729336, 82, 1⟩,
    ⟨260807516, 171, 0⟩,
    ⟨5753000, 177, 1⟩,
    ⟨44259728812, 82, 0⟩,
    ⟨754735656, 68, 1⟩,
    ⟨861912, 195, 0⟩,
    ⟨84792, 171, 1⟩,
    ⟨1058292, 79, 0⟩,
    ⟨47736, 41, 1⟩,
    ⟨1779612, 217, 0⟩,
    ⟨124526784, 66, 0⟩,
    ⟨3583716, 173, 0⟩,
    ⟨90720, 178, 1⟩,
    ⟨3059172, 194, 0⟩,
    ⟨3041160, 203, 2⟩,
    ⟨9345816, 100, 2⟩,
    ⟨2886528, 224, 2⟩,
    ⟨118656528, 67, 0⟩,
    ⟨5654108700, 67, 2⟩,
    ⟨5731128, 213, 2⟩,
    ⟨276580152, 63, 2⟩,
    ⟨323730072, 78, 0⟩,
    ⟨62571600, 193, 0⟩,
    ⟨63365778, 215, 0⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 16.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk16.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk16.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk16
