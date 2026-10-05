import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoData
import MatrixMultiplication.SimplifiedExponentRecurrence

/-!
# Level-two retained-exponent certificate adapter

This module isolates the only finite equality a generated checker must establish at level two:
normalizing each exact recurrence form must give the compact 56-bit coefficient form.  Once those
three integer equalities are supplied, the directed logarithm certificates prove a common lower
bound on all branches and hence on their actual minimum.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelTwoReconstruction

open MatrixMultiplication.Generated.SimplifiedExponentLevelTwo
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRecurrence

noncomputable section

/-- Three exact, decidable coefficient identities connecting the primary-table recurrence to the
compact numerical forms.  This is a reusable generated-data interface, not an analytic premise. -/
structure ExactFormReconstruction : Prop where
  branch0 : Form.normalize (levelTwoBranchForm 0) = Branch0.expectedForm
  branch1 : Form.normalize (levelTwoBranchForm 1) = Branch1.expectedForm
  branch2 : Form.normalize (levelTwoBranchForm 2) = Branch2.expectedForm

theorem commonFloor_le_branchRate (reconstruction : ExactFormReconstruction)
    (coordinate : Fin 3) : commonFloor ≤ levelTwoBranchRate coordinate := by
  fin_cases coordinate
  · change commonFloor ≤ levelTwoBranchRate 0
    rw [← levelTwoBranchForm_eval, ← Form.eval_normalize, reconstruction.branch0]
    exact commonFloor_le_branch0
  · change commonFloor ≤ levelTwoBranchRate 1
    rw [← levelTwoBranchForm_eval, ← Form.eval_normalize, reconstruction.branch1]
    exact commonFloor_le_branch1
  · change commonFloor ≤ levelTwoBranchRate 2
    rw [← levelTwoBranchForm_eval, ← Form.eval_normalize, reconstruction.branch2]
    exact commonFloor_le_branch2

/-- A common directed floor for all three exact branches is a floor for the actual branch
minimum. -/
theorem commonFloor_le_levelTwoRetainedExponent
    (reconstruction : ExactFormReconstruction) :
    commonFloor ≤ levelTwoRetainedExponent := by
  rw [levelTwoRetainedExponent]
  exact le_min (commonFloor_le_branchRate reconstruction 0)
    (le_min (commonFloor_le_branchRate reconstruction 1)
      (commonFloor_le_branchRate reconstruction 2))

end

end MatrixMultiplication.SimplifiedExponentLevelTwoReconstruction
