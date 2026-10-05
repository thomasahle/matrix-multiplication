import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion5
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 5, branch 0, chunk 5, parent 63;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch0.Chunk5.Parent0

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 63

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := -1267650600228229401496703205376
  terms := [⟨3, -475368975085586025561263702016⟩,
      ⟨5, -792281625142643375935439503360⟩,
      ⟨9, 2852213850513516153367582212096⟩,
      ⟨1811, 633825300114114700748351602688⟩,
      ⟨3013, 792281625142643375935439503360⟩,
      ⟨23521, 792281625142643375935439503360⟩,
      ⟨27651, 633825300114114700748351602688⟩,
      ⟨29241, 633825300114114700748351602688⟩,
      ⟨49589, 792281625142643375935439503360⟩,
      ⟨11763217134425, -1426106925256758076683791106048⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 4430, 29241, 49589, 29241, 4430, 256, 4750, 4750][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 4408, 27651, 47042, 27651, 4408, 256, 4633, 4633][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 1811, 3013, 1811, 256, 917, 917, 917, 917][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }]
  referenceNumerators := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 6, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  marginalXNumerators := [0, 0, 4, 10, 4, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 5) (Weights.Region5.dualWeights 63)
    5 5 63

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
        Orientation.order Weights.Region5.dualWeights 5 [parent] 0) =
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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch0.Chunk5.Parent0
