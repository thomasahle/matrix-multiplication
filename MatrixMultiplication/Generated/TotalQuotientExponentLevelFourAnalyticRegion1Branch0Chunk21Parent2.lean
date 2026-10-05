import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 21, parent 88;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk21.Parent2

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 88

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 89290139153575908467924032028672
  terms := [⟨5, -1584563250285286751870879006720⟩,
      ⟨9, -1426106925256758076683791106048⟩,
      ⟨11, -6972078301255261708231867629568⟩,
      ⟨19, -3010670175542044828554670112768⟩,
      ⟨29, -18380933703309326321702196477952⟩,
      ⟨33, 1584563250285286751870879006720⟩,
      ⟨35, -44367771007988029052384612188160⟩,
      ⟨37, -2931442013027780490961126162432⟩,
      ⟨63, -9982748476797306536786537742336⟩,
      ⟨87, -6892850138740997370638323679232⟩,
      ⟨93, -29472876455306333584798349524992⟩,
      ⟨129, 47061528533473016530565106499584⟩,
      ⟨189, -29948245430391919610359613227008⟩,
      ⟨205, 10141204801825835211973625643008⟩,
      ⟨343, 12834962327310822690154119954432⟩,
      ⟨375, 95549163992202791137814004105216⟩,
      ⟨409, 9982748476797306536786537742336⟩,
      ⟨527, -83506483290034611823595323654144⟩,
      ⟨569, -45080824470616408090726507741184⟩,
      ⟨1057, -83744167777577404836375955505152⟩,
      ⟨1917, 83744167777577404836375955505152⟩,
      ⟨2387, 378235247843097947671578818904064⟩,
      ⟨2747, 12914190489825087027747663904768⟩,
      ⟨3819, 83506483290034611823595323654144⟩,
      ⟨8501, 80812725764549624345414829342720⟩,
      ⟨8621, 81921920039749325071724444647424⟩,
      ⟨52662219273, -189117623921548973835789409452032⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[679, 256, 264, 818, 3834, 3819, 820, 264, 256][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[258, 375, 256, 291, 291, 291, 291, 291, 291][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 2747, 8501, 8621, 2744, 256, 1819, 1819, 1819][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 1, y := 2, z := 5 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }, { x := 8, y := 0, z := 0 }]
  referenceNumerators := [1, 9, 1, 87, 37, 2, 372, 569, 116, 116, 560, 378, 2, 38, 88, 1, 9, 1]
  marginalXNumerators := [0, 1, 10, 126, 1057, 1054, 128, 10, 1]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 88)
    1 1 88

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk21.Parent2
