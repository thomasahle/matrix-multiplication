import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 17, parent 73;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 73

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := -5666794323832756746378231047782400
  terms := [⟨5, -6338253001141147007483516026880⟩,
      ⟨7, -1109194275199700726309615304704⟩,
      ⟨27, -8556641551540548460102746636288⟩,
      ⟨31, -2456073037942194465399862460416⟩,
      ⟨39, -6179796676112618332296428126208⟩,
      ⟨51, -64650180611639699476331863474176⟩,
      ⟨53, -4199092613256009892457829367808⟩,
      ⟨55, -4357548938284538567644917268480⟩,
      ⟨71, -45001596308102143753132963790848⟩,
      ⟨79, -6259024838626882669889972076544⟩,
      ⟨129, 89607051803632965818298207830016⟩,
      ⟨411, -260502198346901142007572508704768⟩,
      ⟨461, -36524182919075859630623761104896⟩,
      ⟨465, -36841095569132916980997936906240⟩,
      ⟨469, -148632032876759897325488450830336⟩,
      ⟨579, -45873106095759051466661947244544⟩,
      ⟨801, -63461758173925734412428704219136⟩,
      ⟨927, -146889013301446081898430483922944⟩,
      ⟨991, 731355168169174100326004205551616⟩,
      ⟨999, 731038255519117042975630029750272⟩,
      ⟨1009, 6259024838626882669889972076544⟩,
      ⟨1517, -120189122534139000129406172659712⟩,
      ⟨1519, -120347578859167528804593260560384⟩,
      ⟨1521, 1595259052224712437446007440015360⟩,
      ⟨1657, -262562130572272014785004651413504⟩,
      ⟨1987, 260502198346901142007572508704768⟩,
      ⟨2017, 6179796676112618332296428126208⟩,
      ⟨2307, -731117483681631307313223573700608⟩,
      ⟨2313, 223581874615253960688981027848192⟩,
      ⟨2319, -734920435482315995517713683316736⟩,
      ⟨2335, 224928753377996454428071275003904⟩,
      ⟨2869, -454611196506848769111755187027968⟩,
      ⟨2883, -456829585057248170564374417637376⟩,
      ⟨8005, 262562130572272014785004651413504⟩,
      ⟨8289, 1383878314636655184746432180518912⟩,
      ⟨8317, 1384987508911854885472741795823616⟩,
      ⟨12189, 1353137787581120621760137127788544⟩,
      ⟨16999, -1346799534579979474752653611761664⟩,
      ⟨17079, -1353137787581120621760137127788544⟩,
      ⟨40839, 6471197857840082565965482775543808⟩,
      ⟨97757, 1346799534579979474752653611761664⟩,
      ⟨1396342518295, -3235598928920041282982741387771904⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 2018, 32020, 97757, 97512, 31792, 2017, 256, 6334][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[258, 991, 1521, 999, 256, 630, 630, 630, 630][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 2313, 8289, 8317, 2335, 256, 1703, 1703, 1703][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }]
  referenceNumerators := [1, 0, 32, 40, 7, 568, 1876, 816, 54, 461, 5738, 9228, 1517, 55, 53, 1519, 9276, 5766, 465, 54, 801, 1854, 579, 7, 40, 31, 0, 1]
  marginalXNumerators := [1, 79, 3314, 16999, 17079, 3288, 78, 1, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 73)
    1 1 73

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17.Parent3
