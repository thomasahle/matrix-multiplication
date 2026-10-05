import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 19, parent 79;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19.Parent1

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 79

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 1651035678634754531111862381051904
  terms := [⟨3, -3802951800684688204490109616128⟩,
      ⟨5, -792281625142643375935439503360⟩,
      ⟨7, -1109194275199700726309615304704⟩,
      ⟨15, -4753689750855860255612637020160⟩,
      ⟨61, -4832917913370124593206180970496⟩,
      ⟨71, -45001596308102143753132963790848⟩,
      ⟨77, -12201137027196707989405768351744⟩,
      ⟨83, -6575937488683940020264147877888⟩,
      ⟨87, -6892850138740997370638323679232⟩,
      ⟨143, 445420729655194105950904088788992⟩,
      ⟨151, -11963452539653914976625136500736⟩,
      ⟨239, -37871061681818353369714008260608⟩,
      ⟨349, 792281625142643375935439503360⟩,
      ⟨401, -63540986336439998750022248169472⟩,
      ⟨475, -37633377194275560356933376409600⟩,
      ⟨569, -45080824470616408090726507741184⟩,
      ⟨571, 445024588842622784262936369037312⟩,
      ⟨801, -63461758173925734412428704219136⟩,
      ⟨1001, 11963452539653914976625136500736⟩,
      ⟨1003, 12201137027196707989405768351744⟩,
      ⟨1223, 87943260390833414728833784872960⟩,
      ⟨1575, -124784355959966331709831721779200⟩,
      ⟨1579, -125101268610023389060205897580544⟩,
      ⟨1703, -269851121523584333843610694844416⟩,
      ⟨1941, -615127453760748317076275230408704⟩,
      ⟨2439, 87864032228319150391240240922624⟩,
      ⟨2969, -235228414504850818315231988547584⟩,
      ⟨2973, -235545327154907875665606164348928⟩,
      ⟨3405, -269771893361070069506017150894080⟩,
      ⟨7137, 929980171592434794673018889043968⟩,
      ⟨14021, 2221716133225000554798159455322112⟩,
      ⟨18917, 235228414504850818315231988547584⟩,
      ⟨18931, 235545327154907875665606164348928⟩,
      ⟨19665, 615127453760748317076275230408704⟩,
      ⟨662936003109, -1110858066612500277399079727661056⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 349, 2002, 18917, 39330, 18931, 2006, 349, 256][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 2446, 7137, 7137, 2439, 256, 1646, 1646, 1646][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 572, 571, 256, 382, 382, 382, 382, 382][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 5, z := 3 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }, { x := 8, y := 0, z := 0 }]
  referenceNumerators := [0, 1, 4, 7, 61, 83, 24, 569, 1575, 801, 475, 3406, 3405, 478, 802, 1579, 568, 24, 87, 60, 7, 4, 1, 0]
  marginalXNumerators := [0, 5, 151, 2969, 7764, 2973, 154, 5, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 79)
    1 1 79

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19.Parent1
