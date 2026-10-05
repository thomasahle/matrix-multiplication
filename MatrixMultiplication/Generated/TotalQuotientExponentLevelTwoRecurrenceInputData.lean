import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk4
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk5
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk6
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk7
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk8
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk9
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk10
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk11
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk12
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk13
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk14
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk15
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk16
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputChunk17

/-!
# Definition-only total-quotient level-two recurrence inputs

This generated umbrella collects the eighteen 90-record input leaves without importing the
real-valued recurrence or its sparse-table reconstruction proofs.  Exact sufficient-statistic
checkers consume `expectedInputs`; the semantic provenance adapter separately identifies it with
the established recurrence output.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

/-- The eighteen exact recurrence-input blocks, in certificate order. -/
def expectedInputChunks : List (List EdgeInput) :=
  [Chunk0.expectedInputs,
    Chunk1.expectedInputs,
    Chunk2.expectedInputs,
    Chunk3.expectedInputs,
    Chunk4.expectedInputs,
    Chunk5.expectedInputs,
    Chunk6.expectedInputs,
    Chunk7.expectedInputs,
    Chunk8.expectedInputs,
    Chunk9.expectedInputs,
    Chunk10.expectedInputs,
    Chunk11.expectedInputs,
    Chunk12.expectedInputs,
    Chunk13.expectedInputs,
    Chunk14.expectedInputs,
    Chunk15.expectedInputs,
    Chunk16.expectedInputs,
    Chunk17.expectedInputs]

/-- All 1,620 exact recurrence inputs, before sufficient-statistic grouping. -/
def expectedInputs : List EdgeInput := expectedInputChunks.flatten

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput
