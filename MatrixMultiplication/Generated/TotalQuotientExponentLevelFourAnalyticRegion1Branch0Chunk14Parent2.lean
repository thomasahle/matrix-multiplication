import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 14, parent 60;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk14.Parent2

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 60

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 70037695662609674432692852097024
  terms := [⟨5, -792281625142643375935439503360⟩,
      ⟨7, -19965496953594613073573075484672⟩,
      ⟨21, -13310331302396408715715383656448⟩,
      ⟨27, -2139160387885137115025686659072⟩,
      ⟨35, -11091942751997007263096153047040⟩,
      ⟨41, -12993418652339351365341207855104⟩,
      ⟨137, -10854258264454214250315521196032⟩,
      ⟨225, -17826336565709475958547388825600⟩,
      ⟨257, 31453580518162942024636948283392⟩,
      ⟨269, 158456325028528675187087900672⟩,
      ⟨449, -35573444968904687579501233700864⟩,
      ⟨531, 2456073037942194465399862460416⟩,
      ⟨791, 125338953097566182072986529431552⟩,
      ⟨1063, 2535301200456458802993406410752⟩,
      ⟨2151, 396140812571321687967719751680⟩,
      ⟨4303, 396140812571321687967719751680⟩,
      ⟨4959, 28680594830163690208862910021632⟩,
      ⟨4967, 28839051155192218884049997922304⟩,
      ⟨31355, 12993418652339351365341207855104⟩,
      ⟨31469, 13310331302396408715715383656448⟩,
      ⟨56695, 35573444968904687579501233700864⟩,
      ⟨244451649733, -62669476548783091036493264715776⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 4303, 31469, 56695, 31355, 4302, 256, 4901, 4901][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[777, 256, 269, 1062, 4959, 4967, 1063, 269, 256][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 257, 256, 256, 256, 256, 256, 256, 256][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 8, z := 0 }, { x := 0, y := 7, z := 1 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }]
  referenceNumerators := [0, 0, 1, 4, 28, 140, 224, 225, 137, 27, 4, 1, 0, 0]
  marginalXNumerators := [0, 5, 168, 449, 164, 5, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 60)
    1 1 60

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk14.Parent2
