import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 20, parent 85;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk20.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 85

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 1450429971148637228325009098801152
  terms := [⟨3, -475368975085586025561263702016⟩,
      ⟨5, -6338253001141147007483516026880⟩,
      ⟨7, -554597137599850363154807652352⟩,
      ⟨9, -713053462628379038341895553024⟩,
      ⟨15, -9507379501711720511225274040320⟩,
      ⟨31, -9824292151768777861599449841664⟩,
      ⟨37, -2931442013027780490961126162432⟩,
      ⟨39, -3089898338056309166148214063104⟩,
      ⟨41, -6496709326169675682670603927552⟩,
      ⟨127, -10061976639311570874380081692672⟩,
      ⟨129, -10220432964340099549567169593344⟩,
      ⟨141, -44684683658045086402758787989504⟩,
      ⟨181, -28680594830163690208862910021632⟩,
      ⟨257, 46348475070844637492223210946560⟩,
      ⟨265, 1346878762742493739090247155712⟩,
      ⟨283, -44843139983073615077945875890176⟩,
      ⟨297, 376492228267784132244520851996672⟩,
      ⟨363, 95707620317231319813001092005888⟩,
      ⟨365, -28918279317706483221643541872640⟩,
      ⟨493, 9507379501711720511225274040320⟩,
      ⟨529, -83823395940091669173969499455488⟩,
      ⟨989, 9824292151768777861599449841664⟩,
      ⟨1055, -83585711452548876161188867604480⟩,
      ⟨1121, 13627243952453466066089559457792⟩,
      ⟨1249, 83823395940091669173969499455488⟩,
      ⟨2245, 13864928439996259078870191308800⟩,
      ⟨2491, 83585711452548876161188867604480⟩,
      ⟨6431, 79861987814378452294292301938688⟩,
      ⟨6451, 80099672301921245307072933789696⟩,
      ⟨50945086185, -188246114133892066122260425998336⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[760, 256, 265, 986, 4982, 4996, 989, 265, 256][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 2245, 6431, 6451, 2242, 256, 1547, 1547, 1547][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[257, 363, 256, 288, 288, 288, 288, 288, 288][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 1, y := 5, z := 2 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }, { x := 8, y := 0, z := 0 }]
  referenceNumerators := [1, 1, 8, 3, 37, 80, 127, 566, 362, 365, 564, 129, 82, 39, 3, 7, 1, 1]
  marginalXNumerators := [0, 1, 9, 120, 1055, 1058, 124, 8, 1]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 85)
    1 1 85

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk20.Parent3
