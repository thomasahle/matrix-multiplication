import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 18, parent 76;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18.Parent2

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 76

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 814544738809151654799225353404416
  terms := [⟨7, -5545971375998503631548076523520⟩,
      ⟨13, -4119864450741745554864285417472⟩,
      ⟨55, -17430195753138154270579669073920⟩,
      ⟨59, -4674461588341595918019093069824⟩,
      ⟨63, -4991374238398653268393268871168⟩,
      ⟨219, -17350967590623889932986125123584⟩,
      ⟨257, 66947797324553365266544638033920⟩,
      ⟨281, -44526227333016557727571700088832⟩,
      ⟨561, -44446999170502293389978156138496⟩,
      ⟨781, -123754389847280895321115650424832⟩,
      ⟨1685, 266998907673070817690243112632320⟩,
      ⟨1931, 79228162514264337593543950336⟩,
      ⟨2255, 554597137599850363154807652352⟩,
      ⟨2257, 633825300114114700748351602688⟩,
      ⟨3979, 61877194923640447660557825212416⟩,
      ⟨9095, 21550060203879899825443954491392⟩,
      ⟨15925, 61877194923640447660557825212416⟩,
      ⟨18229, 21787744691422692838224586342400⟩,
      ⟨27969, 4674461588341595918019093069824⟩,
      ⟨28049, 4991374238398653268393268871168⟩,
      ⟨44971, 88973226503518851117549856227328⟩,
      ⟨2212447993839, -133499453836535408845121556316160⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 1929, 28049, 127400, 127328, 27969, 1931, 256, 6479][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 257, 257, 257, 257, 257, 257, 257, 257][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 443, 2257, 18190, 44971, 18229, 2255, 443, 256][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 1, z := 7 }, { x := 0, y := 0, z := 8 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }]
  referenceNumerators := [0, 0, 0, 0, 56, 7, 562, 219, 220, 561, 7, 52, 0, 1, 0, 0]
  marginalXNumerators := [0, 0, 63, 781, 781, 59, 1, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 76)
    1 1 76

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18.Parent2
