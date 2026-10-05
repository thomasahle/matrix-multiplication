import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk4

/-!
# Total-quotient grouped level-two proof chunk 4

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk4

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨227748, 195, 0⟩,
    ⟨205464, 171, 1⟩,
    ⟨108997854, 203, 2⟩,
    ⟨56584731, 78, 0⟩,
    ⟨79304400, 41, 1⟩,
    ⟨1373924385, 100, 2⟩,
    ⟨95760, 217, 0⟩,
    ⟨215054682, 224, 2⟩,
    ⟨13181109, 67, 0⟩,
    ⟨102312, 82, 1⟩,
    ⟨360768000, 67, 2⟩,
    ⟨328020, 173, 0⟩,
    ⟨336336, 178, 1⟩,
    ⟨58736268, 213, 2⟩,
    ⟨4029278628, 82, 0⟩,
    ⟨23094960, 68, 1⟩,
    ⟨510477948, 63, 2⟩,
    ⟨95388, 218, 0⟩,
    ⟨123450, 174, 0⟩,
    ⟨1145664, 79, 0⟩,
    ⟨4613790, 194, 0⟩,
    ⟨6777780, 215, 0⟩,
    ⟨2286480, 172, 0⟩,
    ⟨214325856750, 59, 2⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 4.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk4.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk4.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk4
