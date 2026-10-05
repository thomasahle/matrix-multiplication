import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 18, parent 77;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 77

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 308752149318088123602040774459392
  terms := [⟨3, -475368975085586025561263702016⟩,
      ⟨7, -1663791412799551089464422957056⟩,
      ⟨13, -4119864450741745554864285417472⟩,
      ⟨27, -4278320775770274230051373318144⟩,
      ⟨129, 68373904249810123343228429139968⟩,
      ⟨131, -20757778578737256449508514988032⟩,
      ⟨157, -24877643029479002004372800405504⟩,
      ⟨251, -19886268791080348735979531534336⟩,
      ⟨269, 554597137599850363154807652352⟩,
      ⟨305, -24164589566850622966030904852480⟩,
      ⟨539, -42703979595188477962920189231104⟩,
      ⟨541, -85724871840434013276214554263552⟩,
      ⟨543, -43020892245245535313294365032448⟩,
      ⟨891, 79228162514264337593543950336⟩,
      ⟨1715, 271752597423926677945855749652480⟩,
      ⟨2151, 554597137599850363154807652352⟩,
      ⟨4797, 24877643029479002004372800405504⟩,
      ⟨6091, 4753689750855860255612637020160⟩,
      ⟨14143, 63778670823982791762802880020480⟩,
      ⟨19025, 24164589566850622966030904852480⟩,
      ⟨24343, 4674461588341595918019093069824⟩,
      ⟨45911, 85724871840434013276214554263552⟩,
      ⟨111337, 62590248386268826698899720765440⟩,
      ⟨502429911281, -135876298711963338972927874826240⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 350, 2152, 19025, 45911, 19188, 2151, 350, 256][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 1780, 24343, 113144, 111337, 24364, 1782, 256, 5942][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[258, 256, 257, 257, 257, 257, 257, 257, 257][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 7, z := 1 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }, { x := 8, y := 0, z := 0 }]
  referenceNumerators := [0, 0, 0, 1, 6, 54, 251, 539, 543, 262, 52, 7, 0, 0, 0, 0]
  marginalXNumerators := [0, 0, 7, 305, 1082, 314, 7, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 77)
    1 1 77

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18.Parent3
