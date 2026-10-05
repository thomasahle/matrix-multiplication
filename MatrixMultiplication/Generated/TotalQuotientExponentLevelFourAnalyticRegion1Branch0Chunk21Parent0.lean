import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 21, parent 86;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk21.Parent0

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 86

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 460711765020447123106458071203840
  terms := [⟨3, -2852213850513516153367582212096⟩,
      ⟨5, -6338253001141147007483516026880⟩,
      ⟨7, -8873554201597605810476922437632⟩,
      ⟨9, -1426106925256758076683791106048⟩,
      ⟨15, -4753689750855860255612637020160⟩,
      ⟨21, -3327582825599102178928845914112⟩,
      ⟨41, -6496709326169675682670603927552⟩,
      ⟨51, -8081272576454962434541482934272⟩,
      ⟨101, -64016355311525584775583511871488⟩,
      ⟨107, -16954826778052568245018405371904⟩,
      ⟨109, -8635869714054812797696290586624⟩,
      ⟨129, 30423614405477505635920876929024⟩,
      ⟨135, -42783207757702742300513733181440⟩,
      ⟨219, -17350967590623889932986125123584⟩,
      ⟨225, -17826336565709475958547388825600⟩,
      ⟨231, -18301705540795061984108652527616⟩,
      ⟨267, 475368975085586025561263702016⟩,
      ⟨289, 236971434080164633742289955454976⟩,
      ⟨501, 70671520962723789133441203699712⟩,
      ⟨541, -42862435920217006638107277131776⟩,
      ⟨783, 141263813762933313929288863449088⟩,
      ⟨813, -64412496124096906463551231623168⟩,
      ⟨923, 16954826778052568245018405371904⟩,
      ⟨927, 17350967590623889932986125123584⟩,
      ⟨993, 69720783012552617082318676295680⟩,
      ⟨1629, -129062676735736605939883095097344⟩,
      ⟨1641, -130013414685907777991005622501376⟩,
      ⟨2323, 129062676735736605939883095097344⟩,
      ⟨2347, 130013414685907777991005622501376⟩,
      ⟨3751, 594369675182011060626766715420672⟩,
      ⟨9587531153, -297184837591005530313383357710336⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[737, 267, 256, 927, 4646, 4694, 923, 256, 267][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 993, 1566, 1002, 256, 634, 634, 634, 634][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[258, 578, 578, 256, 385, 385, 385, 385, 385][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 1, y := 4, z := 3 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }, { x := 8, y := 0, z := 0 }]
  referenceNumerators := [3, 9, 12, 30, 109, 80, 56, 540, 808, 225, 231, 813, 541, 56, 82, 102, 30, 12, 9, 3]
  marginalXNumerators := [0, 3, 21, 219, 1629, 1641, 214, 21, 3]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 86)
    1 1 86

opaque support_eq : actualRootRows.support = expectedRootRows.support := by
  unfold actualRootRows expectedRootRows localRowsFrom
  decide +kernel

opaque reference_eq :
    actualRootRows.referenceNumerators = expectedRootRows.referenceNumerators := by
  unfold actualRootRows expectedRootRows localRowsFrom
  decide +kernel

opaque marginal_eq :
    actualRootRows.marginalXNumerators = expectedRootRows.marginalXNumerators := by
  unfold actualRootRows expectedRootRows localRowsFrom
  decide +kernel

opaque weightX_eq : actualRootRows.weightX = expectedRootRows.weightX := by
  funext value
  fin_cases value <;> decide +kernel

opaque weightY_eq : actualRootRows.weightY = expectedRootRows.weightY := by
  funext value
  fin_cases value <;> decide +kernel

opaque weightZ_eq : actualRootRows.weightZ = expectedRootRows.weightZ := by
  funext value
  fin_cases value <;> decide +kernel

theorem branchForm_eq_expectedRootRows :
    actualRootRows.branchForm referenceBits compatibilityExtraBits 0 =
      expectedRootRows.branchForm referenceBits compatibilityExtraBits 0 :=
  LocalRows.branchForm_zero_congr support_eq reference_eq marginal_eq
    weightX_eq weightY_eq weightZ_eq referenceBits compatibilityExtraBits

/-- Kernel recomputation identifies this parent's primary-table recurrence with its compact
signed-log form. -/
opaque recurrence_structuralPowerCanonical :
    Form.structuralPowerCanonical
      (branchFormOnParentsFrom Top.expectedRows BetaThree.expectedRows
        Orientation.order Weights.Region1.dualWeights 1 [parent] 0) =
      expectedForm := by
  unfold parent
  change Form.structuralPowerCanonical
    (Form.sum [WeightedLocalRows.branchForm referenceBits compatibilityExtraBits
      { outerNumerator := 1, rows := actualRootRows } 0]) = expectedForm
  rw [show WeightedLocalRows.branchForm referenceBits compatibilityExtraBits
      { outerNumerator := 1, rows := actualRootRows } 0 =
        WeightedLocalRows.branchForm referenceBits compatibilityExtraBits
          { outerNumerator := 1, rows := expectedRootRows } 0 by
    unfold WeightedLocalRows.branchForm
    rw [branchForm_eq_expectedRootRows]]
  unfold expectedRootRows emptyCompatibilityRows expectedWeightX expectedWeightY expectedWeightZ
    expectedForm referenceBits compatibilityExtraBits
  decide +kernel

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk21.Parent0
