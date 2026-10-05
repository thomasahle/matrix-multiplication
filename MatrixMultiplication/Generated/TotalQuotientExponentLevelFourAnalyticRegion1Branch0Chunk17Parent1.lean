import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 17, parent 71;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17.Parent1

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 71

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := -2498856245699897207700376193597440
  terms := [⟨3, -475368975085586025561263702016⟩,
      ⟨9, -1426106925256758076683791106048⟩,
      ⟨29, -11488083564568328951063872798720⟩,
      ⟨31, -12280365189710972326999312302080⟩,
      ⟨39, -3089898338056309166148214063104⟩,
      ⟨41, -3248354663084837841335301963776⟩,
      ⟨69, 3089898338056309166148214063104⟩,
      ⟨109, -17271739428109625595392581173248⟩,
      ⟨215, -17034054940566832582611949322240⟩,
      ⟨253, -80178900464435509644666477740032⟩,
      ⟨259, 212014562888171367400323611099136⟩,
      ⟨397, -503257288290607072394191172534272⟩,
      ⟨587, 871351331331879184853796365795328⟩,
      ⟨589, 868816030131422726050802959384576⟩,
      ⟨995, -78832021701693015905576230584320⟩,
      ⟨1149, -273099476186669171684945996808192⟩,
      ⟨1159, -91825440354032367270917438439424⟩,
      ⟨1235, 27571400554963989482553294716928⟩,
      ⟨1259, -99748256605458801030271833473024⟩,
      ⟨1265, -100223625580544387055833097175040⟩,
      ⟨1743, -276189374524725480851094210871296⟩,
      ⟨2211, 3248354663084837841335301963776⟩,
      ⟨2263, -179293331769780195974189959610368⟩,
      ⟨3187, -505000307865920887821249139441664⟩,
      ⟨3485, -276110146362211216513500666920960⟩,
      ⟨4925, 27175259742392667794585574965248⟩,
      ⟨8329, 457542638519876549602716313190400⟩,
      ⟨11315, -896466658848900979870949798051840⟩,
      ⟨11339, -898368134749243323973194852859904⟩,
      ⟨18039, 182066317457779447789963997872128⟩,
      ⟨27295, 4325065391653690189231564248842240⟩,
      ⟨33425, 458493376470047721653838840594432⟩,
      ⟨35519, 179293331769780195974189959610368⟩,
      ⟨65551, 1191116195239450051381339749351424⟩,
      ⟨111299, 898368134749243323973194852859904⟩,
      ⟨112393, 896466658848900979870949798051840⟩,
      ⟨9047730261621, -2162532695826845094615782124421120⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 2208, 35519, 112393, 111299, 36078, 2211, 256, 6899][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 4940, 33425, 65551, 33316, 4925, 256, 5293, 5293][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[259, 587, 589, 256, 389, 389, 389, 389, 389][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }]
  referenceNumerators := [0, 0, 1, 9, 29, 3, 116, 995, 1149, 218, 3486, 6352, 1259, 1265, 6374, 3485, 215, 1159, 1012, 124, 3, 31, 9, 1, 0, 0]
  marginalXNumerators := [0, 39, 2263, 11315, 11339, 2298, 41, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 71)
    1 1 71

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17.Parent1
