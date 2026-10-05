import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 21, parent 87;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk21.Parent1

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 87

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 1111888032725185713787795799015424
  terms := [⟨3, -950737950171172051122527404032⟩,
      ⟨7, -3882179963198952542083653566464⟩,
      ⟨11, -3486039150627630854115933814784⟩,
      ⟨15, -1188422437713965063903159255040⟩,
      ⟨21, -6655165651198204357857691828224⟩,
      ⟨29, -2297616712913665790212774559744⟩,
      ⟨33, 475368975085586025561263702016⟩,
      ⟨43, -6813621976226733033044779728896⟩,
      ⟨51, -129300361223279398952663726948352⟩,
      ⟨53, -4199092613256009892457829367808⟩,
      ⟨55, -21787744691422692838224586342400⟩,
      ⟨103, -8160500738969226772135026884608⟩,
      ⟨105, -8318957063997755447322114785280⟩,
      ⟨113, -17905564728223740296140932775936⟩,
      ⟨117, -18539390028337854996889284378624⟩,
      ⟨213, -67502394462153215629699445686272⟩,
      ⟨215, -17034054940566832582611949322240⟩,
      ⟨257, 38346430656903939395275271962624⟩,
      ⟨263, 67740078949696008642480077537280⟩,
      ⟨265, 129300361223279398952663726948352⟩,
      ⟨289, 119238384583967828078283645255680⟩,
      ⟨419, -66393200186953514903389830381568⟩,
      ⟨471, 597063432707496048104947209732096⟩,
      ⟨513, -40644047369817605185488046522368⟩,
      ⟨571, 118049962146253863014380486000640⟩,
      ⟨863, 17034054940566832582611949322240⟩,
      ⟨867, 17430195753138154270579669073920⟩,
      ⟨1061, 68690816899867180693602604941312⟩,
      ⟨1651, -130805696311050421366941062004736⟩,
      ⟨1753, 147364382276531667923991747624960⟩,
      ⟨2155, 130805696311050421366941062004736⟩,
      ⟨4752926855, -298531716353748024052473604866048⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[707, 264, 256, 863, 4310, 4240, 867, 256, 264][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 571, 578, 257, 384, 384, 384, 384, 384][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[257, 1061, 1753, 1052, 256, 664, 664, 664, 664][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 1, y := 3, z := 4 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }, { x := 8, y := 0, z := 0 }]
  referenceNumerators := [3, 14, 8, 84, 103, 28, 234, 852, 512, 53, 55, 513, 838, 226, 29, 105, 86, 7, 15, 3]
  marginalXNumerators := [0, 3, 22, 215, 1651, 1632, 220, 22, 3]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 87)
    1 1 87

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk21.Parent1
