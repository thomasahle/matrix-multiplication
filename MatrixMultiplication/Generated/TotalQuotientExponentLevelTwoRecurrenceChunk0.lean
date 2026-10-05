/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoMassThreeData
import MatrixMultiplication.SimplifiedExponentRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk0Part0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk0Part1
import MatrixMultiplication.SimplifiedExponentLevelTwoInputSemantics

/-!
# Exact level-two recurrence inputs, archived total-weight chunk 0

This is the 90-record recurrence slice for the archived certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
The predecessor artifact is identified in `better_bound/paper.tex:3560-3563`
(the file-inventory appendix); its arithmetic is retained for diagnostics, not as a proved
exponent endpoint. The recursive split parameters follow [alman2025more],
`papers/sources/2404.16349/constituent.tex:41-47`.

Proof sketch: project the full primary table to the three families read by the lightweight
recurrence, identify its literal masses and edge addresses, and compose the two already checked
45-record slices. The semantic bridge is proved once; this module performs no new numerical
recurrence reduction and makes no extraction or feasibility claim.

## Reference

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
-/

set_option autoImplicit false

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk0

open MatrixMultiplication.Generated.TotalQuotientPrimary
open MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRecurrence
open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-- The original 90 exact edge records, in their stored order. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨51987000, 63, 2⟩,
    ⟨4694144, 213, 2⟩,
    ⟨49172448, 67, 2⟩,
    ⟨5416320, 224, 2⟩,
    ⟨4510214800, 100, 2⟩,
    ⟨7079904, 203, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 2⟩,
    ⟨92570400, 63, 2⟩,
    ⟨2798640, 68, 1⟩,
    ⟨1422504, 213, 2⟩,
    ⟨78936, 178, 1⟩,
    ⟨32012400, 67, 2⟩,
    ⟨1075320, 82, 1⟩,
    ⟨299376, 224, 2⟩,
    ⟨32832, 171, 1⟩,
    ⟨357192, 100, 2⟩,
    ⟨36828, 41, 1⟩,
    ⟨327240, 203, 2⟩,
    ⟨33720, 171, 1⟩,
    ⟨240043392162, 68, 2⟩,
    ⟨4354528656, 68, 1⟩,
    ⟨58783947, 213, 2⟩,
    ⟨2577643, 177, 1⟩,
    ⟨6783763290, 67, 2⟩,
    ⟨152149370, 82, 1⟩,
    ⟨57118744, 224, 2⟩,
    ⟨2691698, 170, 1⟩,
    ⟨58601459, 100, 2⟩,
    ⟨2440777, 41, 1⟩,
    ⟨58761136, 203, 2⟩,
    ⟨2349533, 170, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨0, 0, 2⟩,
    ⟨0, 0, 1⟩,
    ⟨191282400, 63, 2⟩,
    ⟨6026400, 68, 1⟩,
    ⟨2040192, 213, 2⟩,
    ⟨118800, 178, 1⟩,
    ⟨57855696, 67, 2⟩,
    ⟨2039856, 82, 1⟩
  ]

/-- The full evaluator returns exactly the stored input slice. -/
opaque inputs_eq :
    edgeInputRangeWithMassThree MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables MassThree.expectedNumerators
        MassThree.expectedActiveEdges.toList 0 90 =
      expectedInputs := by
  have htables :
      MatrixMultiplication.SimplifiedExponentLevelTwoInput.ofPrimaryTables
          MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables =
        MatrixMultiplication.TotalQuotientExponentLevelTwoInputData.tables := by
    unfold MatrixMultiplication.SimplifiedExponentLevelTwoInput.ofPrimaryTables
      MatrixMultiplication.TotalQuotientVolumeReconstruction.primaryTables
      MatrixMultiplication.TotalQuotientExponentLevelTwoInputData.tables
      MatrixMultiplication.Generated.TotalQuotientPrimary.pos3AChunks
      MatrixMultiplication.Generated.TotalQuotientPrimary.pos3AlphaChunks
      MatrixMultiplication.Generated.TotalQuotientPrimary.muChunks
    rw [MatrixMultiplication.Generated.TotalQuotientPrimary.Pos3AData0.data_eq_rawData,
      MatrixMultiplication.Generated.TotalQuotientPrimary.Pos3AlphaData0.data_eq_rawData,
      MatrixMultiplication.Generated.TotalQuotientPrimary.Pos3AlphaData1.data_eq_rawData,
      MatrixMultiplication.Generated.TotalQuotientPrimary.MuData0.data_eq_rawData]
  have hmass :
      MassThree.expectedNumerators =
        MatrixMultiplication.TotalQuotientExponentLevelTwoInputData.massThree := rfl
  have hedges :
      MassThree.expectedActiveEdges =
        MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdgeData.expectedActiveEdges := rfl
  have htarget :
      TotalQuotientExponentLevelTwoRecurrenceInput.Chunk0.expectedInputs =
        expectedInputs := rfl
  rw [MatrixMultiplication.SimplifiedExponentLevelTwoInput.edgeInputRangeWithMassThree_eq,
    htables, hmass, hedges]
  rw [show 90 = 45 + 45 from rfl,
    MatrixMultiplication.SimplifiedExponentLevelTwoInput.edgeInputRangeWithMassThree_add,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk0Part0.inputs_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoInputCheckChunk0Part1.inputs_eq,
    List.take_append_drop]
  exact htarget

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk0
