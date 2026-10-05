import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 12, parent 53;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk12.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 53

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := -2092495000164235420183089272324096
  terms := [⟨7, -9982748476797306536786537742336⟩,
      ⟨9, -2852213850513516153367582212096⟩,
      ⟨13, -2059932225370872777432142708736⟩,
      ⟨19, -3010670175542044828554670112768⟩,
      ⟨27, -2139160387885137115025686659072⟩,
      ⟨35, -5545971375998503631548076523520⟩,
      ⟨67, -15924860665367131856302334017536⟩,
      ⟨81, -25669924654621645380308239908864⟩,
      ⟨121, 695781723200269412746502971850752⟩,
      ⟨131, -10378889289368628224754257494016⟩,
      ⟨239, 1677180972264461762517731884662784⟩,
      ⟨243, 693801019137412804306664373092352⟩,
      ⟨257, 96499901942373963188936531509248⟩,
      ⟨327, -25907609142164438393088871759872⟩,
      ⟨495, -1254974094225947107481736173322240⟩,
      ⟨511, -80971182089578153020601917243392⟩,
      ⟨579, 5466743213484239293954532573184⟩,
      ⟨659, -52211359096900198474145463271424⟩,
      ⟨661, -52369815421928727149332551172096⟩,
      ⟨1023, -81050410252092417358195461193728⟩,
      ⟨1069, -84694905727748576887498482909184⟩,
      ⟨1075, -85170274702834162913059746611200⟩,
      ⟨1113, -705447559027009661932915333791744⟩,
      ⟨1365, -216292883663941641630374984417280⟩,
      ⟨1545, 352723779513504830966457666895872⟩,
      ⟨2319, 5704427701027032306735164424192⟩,
      ⟨2733, -216530568151484434643155616268288⟩,
      ⟨2969, 1254974094225947107481736173322240⟩,
      ⟨3083, 352723779513504830966457666895872⟩,
      ⟨4865, -385445010631896002392591318384640⟩,
      ⟨4879, -386554204907095703118900933689344⟩,
      ⟨5901, 1256717113801260922908794140229632⟩,
      ⟨7931, -1256717113801260922908794140229632⟩,
      ⟨9549, -756549723848710159680751181758464⟩,
      ⟨9561, -757500461798881331731873709162496⟩,
      ⟨30947, 195852017735261442531240645230592⟩,
      ⟨31009, 196485843035375557231988996833280⟩,
      ⟨36249, 1416916458405103413522940007809024⟩,
      ⟨40871, 6476268460240995483571469588365312⟩,
      ⟨145809, 1417391827380188999548501271511040⟩,
      ⟨1733927750201, -3238134230120497741785734794182656⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 3090, 5938, 5901, 3083, 257, 1673, 1673, 1673][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 2316, 30947, 145809, 144996, 31009, 2319, 256, 7190][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[257, 968, 1912, 972, 256, 653, 653, 653, 653][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 7, z := 1 }, { x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }]
  referenceNumerators := [1, 7, 56, 67, 1, 38, 1022, 2730, 661, 27, 1075, 9549, 4865, 324, 327, 4879, 9561, 1069, 26, 659, 2733, 1023, 36, 1, 70, 56, 7, 1]
  marginalXNumerators := [131, 4452, 15840, 15862, 4452, 134, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 53)
    1 1 53

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk12.Parent3
