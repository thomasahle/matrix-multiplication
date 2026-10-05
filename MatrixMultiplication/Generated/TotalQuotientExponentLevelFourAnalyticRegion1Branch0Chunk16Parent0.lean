import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 16, parent 66;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk16.Parent0

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 66

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 10801809220869771258828595100909568
  terms := [⟨3, -475368975085586025561263702016⟩,
      ⟨9, -713053462628379038341895553024⟩,
      ⟨13, -2059932225370872777432142708736⟩,
      ⟨27, -2139160387885137115025686659072⟩,
      ⟨31, -9824292151768777861599449841664⟩,
      ⟨69, 835777886362974497274295132094464⟩,
      ⟨87, -55142801109927978965106589433856⟩,
      ⟨93, -29472876455306333584798349524992⟩,
      ⟨119, -47140756695987280868158650449920⟩,
      ⟨171, -54192063159756806913984062029824⟩,
      ⟨207, -524807348494486972219635127025664⟩,
      ⟨253, -40089450232217754822333238870016⟩,
      ⟨305, 40089450232217754822333238870016⟩,
      ⟨369, -29235191967763540572017717673984⟩,
      ⟨413, -523539697894258742818138423820288⟩,
      ⟨479, -37950289844332617707307552210944⟩,
      ⟨497, -39376396769589375783991343316992⟩,
      ⟨555, 838313187563430956077288538505216⟩,
      ⟨925, -146572100651389024548056308121600⟩,
      ⟨951, 2931442013027780490961126162432⟩,
      ⟨1867, -147918979414131518287146555277312⟩,
      ⟨1897, 2772985687999251815774038261760⟩,
      ⟨2069, 524807348494486972219635127025664⟩,
      ⟨4035, -319685635745056602189949839605760⟩,
      ⟨4047, -320636373695227774241072367009792⟩,
      ⟨4109, 523539697894258742818138423820288⟩,
      ⟨4849, 39376396769589375783991343316992⟩,
      ⟨5701, -451679754493820988620794060865536⟩,
      ⟨5705, -451996667143878045971168236666880⟩,
      ⟨6651, 4215572071058976874677286509477888⟩,
      ⟨12361, -979339316838821476993796770103296⟩,
      ⟨22709, 101966645155858202482891064082432⟩,
      ⟨22811, 102758926781000845858826503585792⟩,
      ⟨45439, 979339316838821476993796770103296⟩,
      ⟨123227, 947489595508087213281192102068224⟩,
      ⟨124011, 949707984058486614733811332677632⟩,
      ⟨7328963452393, -2107786035529488437338643254738944⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 4849, 33104, 45439, 32872, 4880, 256, 4987, 4987][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 555, 552, 256, 377, 377, 377, 377, 377][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 1902, 22709, 124011, 123227, 22811, 1897, 256, 6082][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 0, y := 1, z := 7 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }]
  referenceNumerators := [3, 1, 0, 369, 119, 8, 1, 1867, 4035, 696, 26, 476, 5701, 5705, 479, 27, 684, 4047, 1850, 1, 9, 124, 372, 0, 1, 3]
  marginalXNumerators := [4, 497, 6624, 12361, 6608, 506, 4, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 66)
    1 1 66

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk16.Parent0
