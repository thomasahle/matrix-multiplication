import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk15

/-!
# Total-quotient grouped level-two proof chunk 15

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk15

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨4894584, 194, 0⟩,
    ⟨1112442, 171, 1⟩,
    ⟨1426836930, 79, 0⟩,
    ⟨221169727, 41, 1⟩,
    ⟨267930, 217, 0⟩,
    ⟨790555842, 67, 0⟩,
    ⟨182906406, 82, 1⟩,
    ⟨1320576, 173, 0⟩,
    ⟨1063950, 178, 1⟩,
    ⟨310748214, 82, 0⟩,
    ⟨49430766, 68, 1⟩,
    ⟨2614332, 216, 0⟩,
    ⟨60951899, 170, 1⟩,
    ⟨822130932, 66, 0⟩,
    ⟨360070513, 193, 0⟩,
    ⟨1193470924204, 75, 0⟩,
    ⟨194625427360, 72, 1⟩,
    ⟨361228296, 171, 0⟩,
    ⟨59783704, 177, 1⟩,
    ⟨285232051398, 80, 0⟩,
    ⟨47122399618, 66, 1⟩,
    ⟨5817252, 172, 0⟩,
    ⟨125832, 203, 2⟩,
    ⟨95340, 100, 2⟩,
    ⟨101220, 224, 2⟩,
    ⟨51458988, 67, 2⟩,
    ⟨234192, 213, 2⟩,
    ⟨100380, 63, 2⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 15.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk15.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk15.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk15
