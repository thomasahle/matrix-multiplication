import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk5

/-!
# Total-quotient grouped level-two proof chunk 5

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk5

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨244008, 195, 0⟩,
    ⟨339054, 171, 1⟩,
    ⟨675373656, 203, 2⟩,
    ⟨143752032, 78, 0⟩,
    ⟨204365472, 41, 1⟩,
    ⟨2798736696, 100, 2⟩,
    ⟨217098, 217, 0⟩,
    ⟨1618068, 224, 2⟩,
    ⟨71907408, 67, 0⟩,
    ⟨63948636, 82, 1⟩,
    ⟨589172687112, 67, 2⟩,
    ⟨326436, 173, 0⟩,
    ⟨339942, 178, 1⟩,
    ⟨672529296, 213, 2⟩,
    ⟨42858203928, 82, 0⟩,
    ⟨11371032, 68, 1⟩,
    ⟨162394200, 63, 2⟩,
    ⟨48141288, 170, 1⟩,
    ⟨46802760, 193, 0⟩,
    ⟨170682260220, 69, 0⟩,
    ⟨143983359180, 75, 1⟩,
    ⟨2172146306040, 68, 2⟩,
    ⟨48876300, 172, 0⟩,
    ⟨52430940, 177, 1⟩,
    ⟨41811749220, 67, 1⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 5.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk5.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk5.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk5
