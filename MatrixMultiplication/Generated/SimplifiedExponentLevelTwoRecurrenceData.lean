import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrenceChunk17
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3
import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoData

/-! Kernel-checked level-two retained-rate reconstruction for certificate
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence

open MatrixMultiplication.Generated.SimplifiedExponentLevelTwo
open MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRecurrence
open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

opaque massThree_expected_eq :
    Mass3.expectedNumerators = MassThree.expectedNumerators := by
  decide

opaque activeEdges_eq :
    activeEdges = MassThree.expectedActiveEdges.toList := by
  decide

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

def expectedInputs : List EdgeInput := expectedInputChunks.flatten

theorem activeInputs_eq_expected :
    activeInputsWithMassThree generatedPrimaryTables MassThree.expectedNumerators =
      expectedInputs := by
  unfold activeInputsWithMassThree activeInputChunksWithMassThree
    activeEdgeInputRangeWithMassThree
  rw [activeEdges_eq]
  unfold expectedInputs expectedInputChunks
  rw [Chunk0.inputs_eq, Chunk1.inputs_eq, Chunk2.inputs_eq, Chunk3.inputs_eq,
    Chunk4.inputs_eq, Chunk5.inputs_eq, Chunk6.inputs_eq, Chunk7.inputs_eq,
    Chunk8.inputs_eq, Chunk9.inputs_eq, Chunk10.inputs_eq, Chunk11.inputs_eq,
    Chunk12.inputs_eq, Chunk13.inputs_eq, Chunk14.inputs_eq, Chunk15.inputs_eq,
    Chunk16.inputs_eq, Chunk17.inputs_eq]

opaque expectedBranch0_normalize :
    Form.normalize (inputBranchForm expectedInputs 0) = Branch0.expectedForm := by
  decide

opaque expectedBranch1_normalize :
    Form.normalize (inputBranchForm expectedInputs 1) = Branch1.expectedForm := by
  decide

opaque expectedBranch2_normalize :
    Form.normalize (inputBranchForm expectedInputs 2) = Branch2.expectedForm := by
  decide

theorem reconstructedBranch0_eq_expected :
    reconstructedBranchRate 0 =
      Form.eval levelTwoFormBits Branch0.expectedForm := by
  unfold reconstructedBranchRate
  rw [← activeBranchFormWithMassThree_eval]
  rw [Mass3.recurrence_eq, massThree_expected_eq]
  unfold activeBranchFormWithMassThree
  rw [activeInputs_eq_expected]
  exact Form.eval_eq_of_normalize_eq expectedBranch0_normalize levelTwoFormBits

theorem reconstructedBranch1_eq_expected :
    reconstructedBranchRate 1 =
      Form.eval levelTwoFormBits Branch1.expectedForm := by
  unfold reconstructedBranchRate
  rw [← activeBranchFormWithMassThree_eval]
  rw [Mass3.recurrence_eq, massThree_expected_eq]
  unfold activeBranchFormWithMassThree
  rw [activeInputs_eq_expected]
  exact Form.eval_eq_of_normalize_eq expectedBranch1_normalize levelTwoFormBits

theorem reconstructedBranch2_eq_expected :
    reconstructedBranchRate 2 =
      Form.eval levelTwoFormBits Branch2.expectedForm := by
  unfold reconstructedBranchRate
  rw [← activeBranchFormWithMassThree_eval]
  rw [Mass3.recurrence_eq, massThree_expected_eq]
  unfold activeBranchFormWithMassThree
  rw [activeInputs_eq_expected]
  exact Form.eval_eq_of_normalize_eq expectedBranch2_normalize levelTwoFormBits


theorem commonFloor_le_reconstructedBranchRate (coordinate : Fin 3) :
    commonFloor ≤ reconstructedBranchRate coordinate := by
  fin_cases coordinate
  · rw [reconstructedBranch0_eq_expected]
    exact commonFloor_le_branch0
  · rw [reconstructedBranch1_eq_expected]
    exact commonFloor_le_branch1
  · rw [reconstructedBranch2_eq_expected]
    exact commonFloor_le_branch2

theorem commonFloor_le_reconstructedRetainedExponent :
    commonFloor ≤ reconstructedRetainedExponent := by
  rw [reconstructedRetainedExponent]
  exact le_min (commonFloor_le_reconstructedBranchRate 0)
    (le_min (commonFloor_le_reconstructedBranchRate 1)
      (commonFloor_le_reconstructedBranchRate 2))

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwoRecurrence
