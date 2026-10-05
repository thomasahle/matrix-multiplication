import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk14

/-!
# Total-quotient grouped level-two proof chunk 14

This generated proof leaf groups 90 exact recurrence records from certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` by the sufficient statistic `(muNumerator, heavyCoordinate)`.  The producer
is untrusted: Lean recomputes the displayed result with the executable grouping fold.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk14

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The nonzero sufficient-statistic groups reconstructed from this 90-record block. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨1118832, 194, 0⟩,
    ⟨712392, 171, 1⟩,
    ⟨48721734, 203, 2⟩,
    ⟨2095032, 79, 0⟩,
    ⟨306396, 41, 1⟩,
    ⟨267168, 100, 2⟩,
    ⟨1814112, 216, 0⟩,
    ⟨230208, 224, 2⟩,
    ⟨781143048, 67, 0⟩,
    ⟨5923925898, 82, 1⟩,
    ⟨6038058564, 67, 2⟩,
    ⟨3016200, 172, 0⟩,
    ⟨364776, 178, 1⟩,
    ⟨331812, 213, 2⟩,
    ⟨3275901504, 82, 0⟩,
    ⟨225274704, 68, 1⟩,
    ⟨208711344, 63, 2⟩,
    ⟨721686154, 193, 0⟩,
    ⟨51935611, 170, 1⟩,
    ⟨745825682888, 77, 0⟩,
    ⟨63644644466, 40, 1⟩,
    ⟨38058857746, 96, 2⟩,
    ⟨84959713800, 68, 0⟩,
    ⟨2145550070040, 75, 0⟩,
    ⟨150712723070, 64, 1⟩,
    ⟨169434800470, 57, 2⟩,
    ⟨694512, 173, 0⟩
  ]

/-- The local sufficient-statistic keys are unique. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every retained local group has positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- Exact grouping check for proof chunk 14.

Proof sketch: unfold the 90 integer triples and the proposed compact list, then use
proof-producing call-by-value normalization to evaluate `groupInputs`. -/
theorem inputs_grouped_eq :
    groupInputs MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk14.expectedInputs = expectedInputs := by
  unfold MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk14.expectedInputs expectedInputs
  decide_cbv

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk14
