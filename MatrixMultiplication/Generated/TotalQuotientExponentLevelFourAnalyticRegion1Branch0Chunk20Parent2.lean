import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 20, parent 84;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk20.Parent2

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 84

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 321507883482884681954601350463488
  terms := [⟨3, -237684487542793012780631851008⟩,
      ⟨7, -4436777100798802905238461218816⟩,
      ⟨29, -18380933703309326321702196477952⟩,
      ⟨31, -2456073037942194465399862460416⟩,
      ⟨35, 2456073037942194465399862460416⟩,
      ⟨89, -28205225855078104183301646319616⟩,
      ⟨129, -20440865928680199099134339186688⟩,
      ⟨227, -17984792890738004633734476726272⟩,
      ⟨257, 31136667868105884674262772482048⟩,
      ⟨289, 158456325028528675187087900672⟩,
      ⟨361, -28601366667649425871269366071296⟩,
      ⟨391, 123912846172309423996302738325504⟩,
      ⟨561, 2535301200456458802993406410752⟩,
      ⟨1335, 28601366667649425871269366071296⟩,
      ⟨1949, 316912650057057350374175801344⟩,
      ⟨3901, 396140812571321687967719751680⟩,
      ⟨5309, 28205225855078104183301646319616⟩,
      ⟨14265, 12438821514739501002186400202752⟩,
      ⟨28521, 12438821514739501002186400202752⟩,
      ⟨52601, 36365726594047330955436673204224⟩,
      ⟨240891301365, -61956423086154711998151369162752⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[815, 256, 289, 1122, 5340, 5309, 1120, 289, 256][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 3898, 28530, 52601, 28521, 3901, 256, 4586, 4586][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 257, 257, 257, 257, 257, 257, 257, 257][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 1, y := 6, z := 1 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }, { x := 8, y := 0, z := 0 }]
  referenceNumerators := [0, 0, 1, 4, 28, 129, 232, 227, 129, 28, 3, 1, 0, 0]
  marginalXNumerators := [0, 0, 1, 32, 361, 356, 31, 1, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 84)
    1 1 84

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk20.Parent2
