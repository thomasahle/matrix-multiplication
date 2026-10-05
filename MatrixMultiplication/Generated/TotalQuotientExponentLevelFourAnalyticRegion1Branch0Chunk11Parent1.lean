import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 11, parent 47;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk11.Parent1

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 47

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 231980059841765980473896686583808
  terms := [⟨3, -475368975085586025561263702016⟩,
      ⟨7, -4991374238398653268393268871168⟩,
      ⟨9, -5704427701027032306735164424192⟩,
      ⟨27, -68453132412324387680821973090304⟩,
      ⟨29, -6892850138740997370638323679232⟩,
      ⟨33, 3406810988113366516522389864448⟩,
      ⟨35, 111711709145112716006896969973760⟩,
      ⟨45, -14261069252567580766837911060480⟩,
      ⟨49, -7764359926397905084167307132928⟩,
      ⟨59, -4674461588341595918019093069824⟩,
      ⟨69, -5466743213484239293954532573184⟩,
      ⟨97, -7685131763883640746573763182592⟩,
      ⟨123, -19490127978509027048011811782656⟩,
      ⟨127, 68453132412324387680821973090304⟩,
      ⟨211, 15053350877710224142773350563840⟩,
      ⟨217, -68770045062381445031196148891648⟩,
      ⟨243, -19252443490966234035231179931648⟩,
      ⟨257, -40723275532331869523081590472704⟩,
      ⟨383, -60688772485926482596654665957376⟩,
      ⟨421, 14894894552681695467586262663168⟩,
      ⟨521, -41277872669931719886236398125056⟩,
      ⟨559, 111394796495055658656522794172416⟩,
      ⟨763, -60451087998383689583874034106368⟩,
      ⟨785, 132311031398821443781218397061120⟩,
      ⟨835, -132311031398821443781218397061120⟩,
      ⟨1021, 68770045062381445031196148891648⟩,
      ⟨2131, 125101268610023389060205897580544⟩,
      ⟨3597, 569967401127617644647955178717184⟩,
      ⟨4297, 126052006560194561111328424984576⟩,
      ⟨4328759059, -284983700563808822323977589358592⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 1021, 1570, 1016, 256, 639, 639, 639, 639][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 559, 560, 256, 379, 379, 379, 379, 379][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[703, 256, 264, 844, 4262, 4297, 842, 264, 256][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 0, y := 1, z := 7 }, { x := 0, y := 0, z := 8 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }]
  referenceNumerators := [58, 29, 8, 3, 243, 521, 90, 14, 72, 763, 766, 69, 14, 90, 514, 246, 3, 7, 28, 59]
  marginalXNumerators := [98, 868, 1670, 864, 97, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 47)
    1 1 47

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk11.Parent1
