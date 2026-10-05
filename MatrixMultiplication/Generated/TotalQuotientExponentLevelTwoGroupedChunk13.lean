import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk13

/-!
# Total-quotient grouped level-two proof chunk 13

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk13

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨2289756, 194, 0⟩,
    ⟨527136, 203, 2⟩,
    ⟨10508280, 79, 0⟩,
    ⟨87383506, 100, 2⟩,
    ⟨1500954, 217, 0⟩,
    ⟨621432, 224, 2⟩,
    ⟨917816928, 67, 0⟩,
    ⟨147279918, 67, 2⟩,
    ⟨5503860, 172, 0⟩,
    ⟨53457968, 213, 2⟩,
    ⟨1114334058, 82, 0⟩,
    ⟨163294008, 63, 2⟩,
    ⟨554284038, 78, 0⟩,
    ⟨1631952, 216, 0⟩,
    ⟨1306266, 173, 0⟩,
    ⟨1175106691000, 75, 0⟩,
    ⟨195965715000, 58, 2⟩,
    ⟨321640000, 171, 0⟩,
    ⟨133578027000, 81, 0⟩,
    ⟨21912099000, 62, 2⟩,
    ⟨566496, 195, 0⟩,
    ⟨4711494, 170, 1⟩,
    ⟨51080580, 41, 1⟩,
    ⟨560520, 82, 1⟩,
    ⟨1286220, 177, 1⟩,
    ⟨368630400, 68, 1⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 13.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk13.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk13.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk13
