import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 19, parent 81;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 81

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 812326350258752253346606122795008
  terms := [⟨3, -1426106925256758076683791106048⟩,
      ⟨5, -792281625142643375935439503360⟩,
      ⟨7, -554597137599850363154807652352⟩,
      ⟨11, -3486039150627630854115933814784⟩,
      ⟨23, -7288990951312319058606043430912⟩,
      ⟨31, -4912146075884388930799724920832⟩,
      ⟨45, -7130534626283790383418955530240⟩,
      ⟨63, -4991374238398653268393268871168⟩,
      ⟨103, -65284005911753814177080215076864⟩,
      ⟨159, -12597277839768029677373488103424⟩,
      ⟨161, -12755734164796558352560576004096⟩,
      ⟨211, -66868569162039100928951094083584⟩,
      ⟨243, -38504886981932468070462359863296⟩,
      ⟨395, 950737950171172051122527404032⟩,
      ⟨457, -36207270269018802280249585303552⟩,
      ⟨467, -36999551894161445656185024806912⟩,
      ⟨491, -38901027794503789758430079614976⟩,
      ⟨567, 440350127254281188344917275967488⟩,
      ⟨569, 440587811741823981357697907818496⟩,
      ⟨617, 80812725764549624345414829342720⟩,
      ⟨735, -232930797791937152525019213987840⟩,
      ⟨1585, -125576637585108975085767161282560⟩,
      ⟨1603, -127002744510365733162450952388608⟩,
      ⟨2001, 12597277839768029677373488103424⟩,
      ⟨2003, 12755734164796558352560576004096⟩,
      ⟨2459, 80495813114492566995040653541376⟩,
      ⟨2937, -232693113304394359512238582136832⟩,
      ⟨3401, -269454980711013012155642975092736⟩,
      ⟨3413, -270405718661184184206765502496768⟩,
      ⟨3823, 467446158834159591801909306982400⟩,
      ⟨3869, -141501498250476106942069495300096⟩,
      ⟨4457, 232693113304394359512238582136832⟩,
      ⟨13947, 2209990365172889432834314950672384⟩,
      ⟨17763, 232930797791937152525019213987840⟩,
      ⟨36925, 613067521535377444298843087699968⟩,
      ⟨330829521043, -1104995182586444716417157475336192⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 395, 2003, 17763, 36925, 17828, 2001, 395, 256][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 567, 569, 256, 381, 381, 381, 381, 381][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 2468, 7646, 7738, 2459, 256, 1693, 1693, 1693][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 3, z := 5 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }, { x := 8, y := 0, z := 0 }]
  referenceNumerators := [0, 5, 1, 92, 63, 6, 824, 1603, 491, 22, 467, 3401, 3413, 457, 22, 486, 1585, 844, 7, 62, 90, 1, 5, 0]
  marginalXNumerators := [0, 6, 161, 2940, 7738, 2937, 159, 6, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 81)
    1 1 81

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19.Parent3
