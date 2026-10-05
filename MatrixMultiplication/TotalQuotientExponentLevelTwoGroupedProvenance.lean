/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk0Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk0Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk1Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk1Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk2Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk2Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk3Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk3Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk4Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk4Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk5Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk5Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk6Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk6Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk7Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk7Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk8Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk8Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk9Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk9Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk10Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk10Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk11Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk11Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk12Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk12Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk13Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk13Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk14Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk14Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk15Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk15Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk16Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk16Part1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk17Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk17Part1
import MatrixMultiplication.SimplifiedExponentLevelTwoInputSemantics
import MatrixMultiplication.SimplifiedExponentRecurrenceGrouping
import MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdges
import MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedData
import MatrixMultiplication.TotalQuotientVolumeReconstructionBase

/-!
# Semantic provenance for the compact total-quotient level-two certificate

The compact checker reduces 1,620 emitted integer records to 67 sufficient-statistic groups.  This
module connects those literals to the established real-valued recurrence without importing the
historical 90-row proof chain:

1. four small equalities identify the three projected sparse table families;
2. an eight-shard certificate identifies the active edge addresses;
3. thirty-six independent 45-row certificates reconstruct every exact edge record; and
4. the generic grouping theorem transports the checked merge to all three semantic branch rates.

The Python producer remains untrusted.  Every table projection, address shard, input slice, local
group, global merge, and semantic preservation step is a kernel-checked theorem.
-/

namespace MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedProvenance

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRecurrence
open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked
open MatrixMultiplication.SimplifiedExponentLevelTwoInput
open MatrixMultiplication.Generated.TotalQuotientPrimary

/-- The full semantic primary table used by the total-quotient recurrence. -/
abbrev certifiedTables :=
  MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables

/-- The dependency-light projection containing exactly the three level-two table families. -/
abbrev inputTables :=
  MatrixMultiplication.TotalQuotientExponentLevelTwoInputData.tables

/-- The checked 270-entry level-three mass cache. -/
abbrev certifiedMassThree :=
  MatrixMultiplication.TotalQuotientExponentLevelTwoInputData.massThree

/-- The checked 1,620-entry active-edge address cache. -/
abbrev certifiedActiveEdges :=
  MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdgeData.expectedActiveEdges.toList

/-- The eighteen emitted exact input blocks. -/
abbrev inputChunks :=
  MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedData.expectedInputChunks

/-- The independently grouped summaries of the eighteen input blocks. -/
abbrev groupedChunks :=
  MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedData.expectedGroupedChunks

/-- The final 67-record sufficient statistic. -/
abbrev groupedInputs :=
  MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedData.expectedInputs

/-- Projecting the full semantic table yields exactly the dependency-light table.

Proof sketch: unfold the four table constructors and use each generated leaf's theorem equating its
checked payload with the raw literal imported by the lightweight checker. -/
theorem inputTables_eq :
    ofPrimaryTables certifiedTables = inputTables := by
  unfold ofPrimaryTables certifiedTables inputTables
    MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables
    MatrixMultiplication.TotalQuotientExponentLevelTwoInputData.tables
    MatrixMultiplication.Generated.TotalQuotientPrimary.pos3AChunks
    MatrixMultiplication.Generated.TotalQuotientPrimary.pos3AlphaChunks
    MatrixMultiplication.Generated.TotalQuotientPrimary.muChunks
  rw [Pos3AData0.data_eq_rawData, Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData, MuData0.data_eq_rawData]

/-- The semantic recurrence enumerates exactly the checked active-edge addresses.

Proof sketch: first transport to the lightweight geometry, then apply its independent eight-shard
finite certificate. -/
theorem semanticActiveEdges_eq :
    MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.activeEdges =
      certifiedActiveEdges := by
  calc
    MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.activeEdges =
        MatrixMultiplication.SimplifiedExponentLevelTwoInput.activeEdges :=
      MatrixMultiplication.SimplifiedExponentLevelTwoInput.activeEdges_eq
    _ = MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdges.cached :=
      MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdges.activeEdges_eq
    _ = certifiedActiveEdges := rfl

/-- Two independently checked consecutive ranges reconstruct their complete target list.

Proof sketch: split the combined range, substitute the checked prefix and suffix, and reassemble
them with `List.take_append_drop`.  Keeping this theorem in the semantic adapter means changes to
the theorem layer do not invalidate any finite certificate leaf. -/
private theorem inputRange_eq_of_halves
    (data : InputTables) (massThree : Array Nat) (edges : List Nat)
    (start left right : Nat) (target : List EdgeInput)
    (hleft : edgeInputRangeWithMassThree data massThree edges start left = target.take left)
    (hright : edgeInputRangeWithMassThree data massThree edges (start + left) right =
      target.drop left) :
    edgeInputRangeWithMassThree data massThree edges start (left + right) = target := by
  rw [edgeInputRangeWithMassThree_add, hleft, hright, List.take_append_drop]


/-- Lightweight sparse-table reconstruction of emitted input chunk 0. -/
theorem inputChunk0_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        0 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk0.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 0 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk0.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk0Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk0Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 1. -/
theorem inputChunk1_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        90 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk1.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 90 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk1.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk1Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk1Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 2. -/
theorem inputChunk2_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        180 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk2.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 180 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk2.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk2Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk2Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 3. -/
theorem inputChunk3_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        270 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk3.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 270 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk3.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk3Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk3Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 4. -/
theorem inputChunk4_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        360 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk4.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 360 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk4.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk4Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk4Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 5. -/
theorem inputChunk5_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        450 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk5.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 450 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk5.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk5Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk5Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 6. -/
theorem inputChunk6_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        540 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk6.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 540 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk6.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk6Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk6Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 7. -/
theorem inputChunk7_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        630 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk7.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 630 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk7.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk7Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk7Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 8. -/
theorem inputChunk8_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        720 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk8.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 720 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk8.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk8Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk8Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 9. -/
theorem inputChunk9_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        810 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk9.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 810 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk9.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk9Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk9Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 10. -/
theorem inputChunk10_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        900 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk10.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 900 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk10.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk10Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk10Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 11. -/
theorem inputChunk11_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        990 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk11.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 990 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk11.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk11Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk11Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 12. -/
theorem inputChunk12_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        1080 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk12.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 1080 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk12.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk12Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk12Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 13. -/
theorem inputChunk13_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        1170 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk13.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 1170 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk13.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk13Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk13Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 14. -/
theorem inputChunk14_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        1260 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk14.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 1260 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk14.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk14Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk14Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 15. -/
theorem inputChunk15_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        1350 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk15.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 1350 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk15.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk15Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk15Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 16. -/
theorem inputChunk16_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        1440 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk16.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 1440 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk16.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk16Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk16Part1.inputs_eq)

/-- Lightweight sparse-table reconstruction of emitted input chunk 17. -/
theorem inputChunk17_eq :
    edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        1530 90 =
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk17.expectedInputs := by
  simpa using
    (inputRange_eq_of_halves inputTables certifiedMassThree
      certifiedActiveEdges 1530 45 45
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.Chunk17.expectedInputs
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk17Part0.inputs_eq
      MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk17Part1.inputs_eq)

/-- Every semantic recurrence range equals its dependency-light reconstruction. -/
theorem semanticRange_eq (start count : Nat) :
    MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeInputRangeWithMassThree
        certifiedTables certifiedMassThree
        MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.activeEdges start count =
      edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        start count := by
  calc
    MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeInputRangeWithMassThree
        certifiedTables certifiedMassThree
        MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.activeEdges start count =
      edgeInputRangeWithMassThree (ofPrimaryTables certifiedTables) certifiedMassThree
        MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.activeEdges start count :=
      edgeInputRangeWithMassThree_eq certifiedTables certifiedMassThree
        MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.activeEdges start count
    _ = edgeInputRangeWithMassThree inputTables certifiedMassThree certifiedActiveEdges
        start count := by rw [inputTables_eq, semanticActiveEdges_eq]

/-- The semantic recurrence's eighteen active-input blocks are the emitted exact blocks.

Proof sketch: unfold only the fixed 18-way range schedule, transport every range through
`semanticRange_eq`, and substitute the 18 theorems assembled from the 36 independent proof
leaves. -/
theorem activeInputChunks_eq_inputChunks :
    activeInputChunksWithMassThree certifiedTables certifiedMassThree = inputChunks := by
  unfold activeInputChunksWithMassThree activeEdgeInputRangeWithMassThree inputChunks
    MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedData.expectedInputChunks
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.expectedInputChunks
  simp only [semanticRange_eq,
    inputChunk0_eq,
    inputChunk1_eq,
    inputChunk2_eq,
    inputChunk3_eq,
    inputChunk4_eq,
    inputChunk5_eq,
    inputChunk6_eq,
    inputChunk7_eq,
    inputChunk8_eq,
    inputChunk9_eq,
    inputChunk10_eq,
    inputChunk11_eq,
    inputChunk12_eq,
    inputChunk13_eq,
    inputChunk14_eq,
    inputChunk15_eq,
    inputChunk16_eq,
    inputChunk17_eq]

/-- The semantic recurrence's full active-input list is the flattening of the emitted blocks. -/
theorem activeInputs_eq_inputChunks :
    activeInputsWithMassThree certifiedTables certifiedMassThree = inputChunks.flatten := by
  unfold activeInputsWithMassThree
  rw [activeInputChunks_eq_inputChunks]

/-- Every original retained-rate branch equals evaluation of the compact 67-record form.

Proof sketch: `activeInputs_eq_inputChunks` supplies table provenance; the generated local checks
group each block; the global merge checks the 67-record list; and the generic grouping theorem
proves preservation of the real branch rate. -/
theorem activeBranchRate_eq_grouped (coordinate : Fin 3) :
    activeBranchRateWithMassThree certifiedTables certifiedMassThree coordinate =
      Form.eval levelTwoFormBits (inputBranchForm groupedInputs coordinate) := by
  exact activeBranchRateWithMassThree_eq_groupedChunkFamily certifiedTables certifiedMassThree
    inputChunks groupedChunks groupedInputs activeInputs_eq_inputChunks
    MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedData.expectedInputChunks_grouped
    MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedData.expectedGroupedChunks_merge
    coordinate

end MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedProvenance
