import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 14, parent 61;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk14.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 61

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := -3286701093741741780730577235738624
  terms := [⟨9, -47061528533473016530565106499584⟩,
      ⟨15, -9507379501711720511225274040320⟩,
      ⟨21, -3327582825599102178928845914112⟩,
      ⟨35, -11091942751997007263096153047040⟩,
      ⟨43, -3406810988113366516522389864448⟩,
      ⟨95, 281101520600609869781893935792128⟩,
      ⟨153, -48487635458729774607248897605632⟩,
      ⟨257, 133657910161563937520308644216832⟩,
      ⟨287, -45476965283187729778694227492864⟩,
      ⟨289, -183175511732979148516273613176832⟩,
      ⟨303, -48012266483644188581687633903616⟩,
      ⟨307, 158456325028528675187087900672⟩,
      ⟨413, -130884924473564685704534605955072⟩,
      ⟨1003, -79465847001807130606324582187008⟩,
      ⟨1007, -79782759651864187956698757988352⟩,
      ⟨1661, -131597977936193064742876501508096⟩,
      ⟨1731, -274287898624383136748849156063232⟩,
      ⟨1951, 4040636288227481217270741467136⟩,
      ⟨1953, 4119864450741745554864285417472⟩,
      ⟨4861, 5545971375998503631548076523520⟩,
      ⟨4863, 5545971375998503631548076523520⟩,
      ⟨6915, 1095725487572275788918712833146880⟩,
      ⟨8245, 98718290492773364641555762118656⟩,
      ⟨16437, 98401377842716307291181586317312⟩,
      ⟨17515, 131597977936193064742876501508096⟩,
      ⟨27505, 274287898624383136748849156063232⟩,
      ⟨34813, 130884924473564685704534605955072⟩,
      ⟨42757, 342424118386650467079296953352192⟩,
      ⟨20669369589, -547862743786137894459356416573440⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 4861, 35030, 55010, 34813, 4863, 256, 5208, 5208][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 307, 1953, 16437, 42757, 16490, 1951, 307, 256][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 380, 257, 293, 293, 293, 293, 293, 293][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 8, z := 0 }, { x := 0, y := 7, z := 1 }, { x := 0, y := 6, z := 2 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }]
  referenceNumerators := [0, 0, 0, 1, 9, 60, 42, 612, 1007, 574, 2312, 576, 1003, 606, 43, 60, 9, 1, 0, 0, 0]
  marginalXNumerators := [0, 70, 1661, 3462, 1652, 70, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 61)
    1 1 61

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk14.Parent3
