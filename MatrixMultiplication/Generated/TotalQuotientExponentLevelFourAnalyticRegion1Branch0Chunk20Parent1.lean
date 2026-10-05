import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 20, parent 83;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk20.Parent1

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 83

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 430605063265026674820911370076160
  terms := [⟨7, -1663791412799551089464422957056⟩,
      ⟨39, -24719186704450473329185712504832⟩,
      ⟨49, -3882179963198952542083653566464⟩,
      ⟨51, -4040636288227481217270741467136⟩,
      ⟨67, -21233147553822842475069778690048⟩,
      ⟨257, 69403870362495559731944500494336⟩,
      ⟨261, -20678550416222992111914971037696⟩,
      ⟨275, -43575489382845385676449172684800⟩,
      ⟨317, -25115327517021795017153432256512⟩,
      ⟨555, -43971630195416707364416892436480⟩,
      ⟨1105, -87547119578262093040866065121280⟩,
      ⟨1749, 277140112474896652902216738275328⟩,
      ⟨1943, 554597137599850363154807652352⟩,
      ⟨1945, 633825300114114700748351602688⟩,
      ⟨2041, 79228162514264337593543950336⟩,
      ⟨3947, 24719186704450473329185712504832⟩,
      ⟨15873, 25115327517021795017153432256512⟩,
      ⟨29041, 4436777100798802905238461218816⟩,
      ⟨29067, 4595233425827331580425549119488⟩,
      ⟨34027, 64254039799068377788364143722496⟩,
      ⟨37143, 87547119578262093040866065121280⟩,
      ⟨137621, 65204777749239549839486671126528⟩,
      ⟨1993381485817, -138570056237448326451108369137664⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 355, 1943, 15788, 37143, 15873, 1945, 355, 256][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[257, 256, 256, 256, 256, 256, 256, 256, 256][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 2041, 29041, 137621, 136108, 29067, 2039, 256, 6751][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 1, z := 7 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }, { x := 8, y := 0, z := 0 }]
  referenceNumerators := [0, 0, 0, 7, 0, 261, 51, 555, 550, 49, 268, 1, 7, 0, 0, 0]
  marginalXNumerators := [0, 0, 7, 312, 1105, 317, 8, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 83)
    1 1 83

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk20.Parent1
