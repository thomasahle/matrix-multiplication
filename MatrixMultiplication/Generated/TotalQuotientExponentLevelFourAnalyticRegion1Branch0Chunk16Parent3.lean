import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 16, parent 69;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk16.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 69

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 231900831679251716136303142633472
  terms := [⟨7, -1109194275199700726309615304704⟩,
      ⟨29, -4595233425827331580425549119488⟩,
      ⟨57, -22580026316565336214160025845760⟩,
      ⟨59, -18697846353366383672076372279296⟩,
      ⟨65, -5149830563427181943580356771840⟩,
      ⟨259, 69403870362495559731944500494336⟩,
      ⟨285, -45160052633130672428320051691520⟩,
      ⟨287, -45476965283187729778694227492864⟩,
      ⟨401, -63540986336439998750022248169472⟩,
      ⟨403, -63857898986497056100396423970816⟩,
      ⟨941, 1267650600228229401496703205376⟩,
      ⟨1739, 275555549224611366150345859268608⟩,
      ⟨1897, 158456325028528675187087900672⟩,
      ⟨4065, 23213851616679450914908377448448⟩,
      ⟨6609, 5149830563427181943580356771840⟩,
      ⟨8071, 22659254479079600551753569796096⟩,
      ⟨13207, 5070602400912917605986812821504⟩,
      ⟨40389, 90637017916318402207014279184384⟩,
      ⟨60451, 63540986336439998750022248169472⟩,
      ⟨121517, 63857898986497056100396423970816⟩,
      ⟨1890405977373, -137777774612305683075172929634304⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 1897, 26414, 121517, 120902, 26436, 1897, 256, 6280][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 302, 1882, 16142, 40389, 16260, 1882, 302, 256][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[259, 256, 258, 258, 258, 258, 258, 258, 258][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 8, z := 0 }, { x := 0, y := 7, z := 1 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }]
  referenceNumerators := [0, 0, 0, 1, 7, 57, 236, 570, 574, 228, 58, 7, 1, 0, 0, 0]
  marginalXNumerators := [0, 1, 64, 806, 802, 65, 1, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 69)
    1 1 69

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk16.Parent3
