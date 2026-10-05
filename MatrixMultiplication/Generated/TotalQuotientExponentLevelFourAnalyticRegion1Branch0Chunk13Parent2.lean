import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 13, parent 56;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13.Parent2

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 56

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := -4948274117990893468742380962185216
  terms := [⟨3, -950737950171172051122527404032⟩,
      ⟨7, -4436777100798802905238461218816⟩,
      ⟨13, -4119864450741745554864285417472⟩,
      ⟨33, -10458117451882892562347801444352⟩,
      ⟨55, -4357548938284538567644917268480⟩,
      ⟨65, 82714201664891968447659884150784⟩,
      ⟨67, -5308286888455710618767444672512⟩,
      ⟨257, 10299661126854363887160713543680⟩,
      ⟨307, -24323045891879151641217992753152⟩,
      ⟨309, -24481502216907680316405080653824⟩,
      ⟨369, -58470383935527081144035435347968⟩,
      ⟨739, -58549612098041345481628979298304⟩,
      ⟨751, -59500350048212517532751506702336⟩,
      ⟨771, -61084913298497804284622385709056⟩,
      ⟨881, -139600022350133762839824440492032⟩,
      ⟨907, 10299661126854363887160713543680⟩,
      ⟨1037, 752667543885511207138667528192000⟩,
      ⟨1043, 753380597348139586177009423745024⟩,
      ⟨1159, -734603522832258938167339507515392⟩,
      ⟨1519, -240695157718335057609186521120768⟩,
      ⟨1523, -241328983018449172309934872723456⟩,
      ⟨1663, 1587653148623343061037027220783104⟩,
      ⟨2285, -362072702690188022802495853035520⟩,
      ⟨2885, 1266462177790515436432800046120960⟩,
      ⟨3051, 362072702690188022802495853035520⟩,
      ⟨3063, 362944212477844930516024836489216⟩,
      ⟨4581, -362944212477844930516024836489216⟩,
      ⟨4639, -735078891807344524192900771217408⟩,
      ⟨5491, -435041840365825477726149831294976⟩,
      ⟨5493, -435200296690854006401336919195648⟩,
      ⟨5757, 1265986808815429850407238782418944⟩,
      ⟨15979, -1265986808815429850407238782418944⟩,
      ⟨15985, -1266462177790515436432800046120960⟩,
      ⟨21975, 157030218103271917110404109565952⟩,
      ⟨22111, 157188674428300445785591197466624⟩,
      ⟨41373, 6555813535405316878515387714502656⟩,
      ⟨131313, 1475782983153201816354943162908672⟩,
      ⟨132081, 1477288318240972838769220497965056⟩,
      ⟨2875307207895, -3277906767702658439257693857251328⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 3051, 5757, 5770, 3063, 257, 1653, 1653, 1653][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[260, 1037, 1663, 1043, 256, 654, 654, 654, 654][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 1814, 21975, 131313, 132081, 22111, 1814, 256, 6060][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 0, y := 1, z := 7 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }]
  referenceNumerators := [66, 55, 6, 1, 751, 3046, 739, 33, 1, 307, 5493, 9272, 881, 26, 26, 881, 9278, 5491, 309, 1, 33, 738, 3038, 771, 1, 6, 56, 67]
  marginalXNumerators := [128, 4570, 15979, 15985, 4581, 130, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 56)
    1 1 56

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13.Parent2
