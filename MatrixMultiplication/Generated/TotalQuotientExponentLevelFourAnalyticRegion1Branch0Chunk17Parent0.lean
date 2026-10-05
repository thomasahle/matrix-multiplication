import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 17, parent 70;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17.Parent0

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 70

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 11535065864939287703256844361269248
  terms := [⟨7, -2218388550399401452619230609408⟩,
      ⟨21, -53241325209585634862861534625792⟩,
      ⟨31, -9824292151768777861599449841664⟩,
      ⟨87, -27571400554963989482553294716928⟩,
      ⟨125, -9903520314283042199192993792000⟩,
      ⟨135, -85566415515405484601027466362880⟩,
      ⟨155, 1571886744283004457855911974666240⟩,
      ⟨179, -113454728720426531433954936881152⟩,
      ⟨257, 184443162333207377917770316382208⟩,
      ⟨341, -27016803417364139119398487064576⟩,
      ⟨405, 417136275637601737430008898519040⟩,
      ⟨671, -53162097047071370525267990675456⟩,
      ⟨713, -112979359745340945408393673179136⟩,
      ⟨1695, 37395692706732767344152744558592⟩,
      ⟨1987, 1267650600228229401496703205376⟩,
      ⟨2049, 1267650600228229401496703205376⟩,
      ⟨2139, -338938079236022836225181019537408⟩,
      ⟨2503, -198308090773203636996640507691008⟩,
      ⟨2511, -198941916073317751697388859293696⟩,
      ⟨4283, -339334220048594157913148739289088⟩,
      ⟨6845, 38029518006846882044901096161280⟩,
      ⟨7461, 339334220048594157913148739289088⟩,
      ⟨30349, 53162097047071370525267990675456⟩,
      ⟨30483, 53241325209585634862861534625792⟩,
      ⟨61007, 354070658276247324705547914051584⟩,
      ⟨119099, 338938079236022836225181019537408⟩,
      ⟨122687, 355179852551447025431857529356288⟩,
      ⟨23611715854665, -785943372141502228927955987333120⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 2049, 30483, 119376, 119099, 30349, 2049, 256, 6605][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 1987, 27120, 122687, 122014, 27380, 1987, 256, 6417][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[257, 405, 256, 299, 299, 299, 299, 299, 299][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 7, z := 1 }, { x := 0, y := 6, z := 2 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }]
  referenceNumerators := [0, 0, 0, 1, 7, 7, 125, 540, 348, 2503, 1432, 1426, 2511, 341, 540, 124, 7, 7, 1, 0, 0, 0]
  marginalXNumerators := [0, 8, 672, 4283, 4278, 671, 8, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 70)
    1 1 70

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17.Parent0
