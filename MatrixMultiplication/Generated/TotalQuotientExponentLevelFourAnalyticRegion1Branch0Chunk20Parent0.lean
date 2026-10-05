import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 20, parent 82;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk20.Parent0

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 82

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 1450271514823608699649822010900480
  terms := [⟨3, -3802951800684688204490109616128⟩,
      ⟨9, -713053462628379038341895553024⟩,
      ⟨25, -3961408125713216879677197516800⟩,
      ⟨47, -3723723638170423866896565665792⟩,
      ⟨51, -4040636288227481217270741467136⟩,
      ⟨59, -9348923176683191836038186139648⟩,
      ⟨129, 136430895849563189336082682478592⟩,
      ⟨175, 158456325028528675187087900672⟩,
      ⟨195, -61797966761126183322964281262080⟩,
      ⟨277, -43892402032902443026823348486144⟩,
      ⟨363, -115039291970711818185825815887872⟩,
      ⟨383, 290846584589864383305899841683456⟩,
      ⟨423, -67027025487067629604138181984256⟩,
      ⟨561, -44446999170502293389978156138496⟩,
      ⟨649, 4516005263313067242832005169152⟩,
      ⟨767, -60768000648440746934248209907712⟩,
      ⟨843, -66789340999524836591357550133248⟩,
      ⟨967, 115039291970711818185825815887872⟩,
      ⟨1447, -114643151158140496497858096136192⟩,
      ⟨1859, 9348923176683191836038186139648⟩,
      ⟨2043, -323726272033284083407220581072896⟩,
      ⟨2539, -201160304623717153150008089903104⟩,
      ⟨3855, 114643151158140496497858096136192⟩,
      ⟨5193, 4516005263313067242832005169152⟩,
      ⟨7105, 1125832189327696237204259534274560⟩,
      ⟨33245, 323726272033284083407220581072896⟩,
      ⟨36777, 109255636107170521541497107513344⟩,
      ⟨36947, 109651776919741843229464827265024⟩,
      ⟨38527, 334976671110309619345503822020608⟩,
      ⟨2744029065539, -562916094663848118602129767137280⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 350, 1859, 15420, 33245, 15472, 1859, 350, 256][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[258, 383, 256, 293, 293, 293, 293, 293, 293][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 5193, 36777, 77054, 36947, 5192, 256, 5655, 5655][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 2, z := 6 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }, { x := 8, y := 0, z := 0 }]
  referenceNumerators := [0, 1, 0, 50, 9, 0, 846, 554, 47, 767, 2539, 780, 48, 561, 843, 0, 8, 51, 0, 1, 0]
  marginalXNumerators := [0, 1, 59, 1447, 4086, 1452, 59, 1, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 82)
    1 1 82

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk20.Parent0
