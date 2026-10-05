import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 7, parent 33;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 33

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 4184039262378299668315056017244160
  terms := [⟨3, -475368975085586025561263702016⟩,
      ⟨13, -2059932225370872777432142708736⟩,
      ⟨27, -2139160387885137115025686659072⟩,
      ⟨53, 804245077682297290912064639860736⟩,
      ⟨105, -8318957063997755447322114785280⟩,
      ⟨157, -49755286058958004008745600811008⟩,
      ⟨203, -257333071846330568503830750691328⟩,
      ⟨287, -181907861132750919114776909971456⟩,
      ⟨303, -48012266483644188581687633903616⟩,
      ⟨317, -25115327517021795017153432256512⟩,
      ⟨321, -25432240167078852367527608057856⟩,
      ⟨425, 814861651459208712149599529205760⟩,
      ⟨489, 2772985687999251815774038261760⟩,
      ⟨601, -47616125671072866893719914151936⟩,
      ⟨635, -50309883196557854371900408463360⟩,
      ⟨1955, 2693757525484987478180494311424⟩,
      ⟨2283, -180877895020065482726060838617088⟩,
      ⟨2425, 34464250693704986853191618396160⟩,
      ⟨3237, -256461562058673660790301767237632⟩,
      ⟨3447, -273099476186669171684945996808192⟩,
      ⟨3453, -273574845161754757710507260510208⟩,
      ⟨4835, 34226566206162193840410986545152⟩,
      ⟨6069, -480835718299070264855218234589184⟩,
      ⟨6083, -481944912574269965581527849893888⟩,
      ⟨10257, -812643262908809310696980298596352⟩,
      ⟨10285, -814861651459208712149599529205760⟩,
      ⟨16995, 507456380903863082286649001902080⟩,
      ⟨23705, 106007281444085683700161805549568⟩,
      ⟨23835, 106878791231742591413690789003264⟩,
      ⟨27027, 4282599096546044504281424691462144⟩,
      ⟨33825, 506267958466149117222745842647040⟩,
      ⟨57611, 1058409023028057285912153632538624⟩,
      ⟨65547, 961354523948083472360062293377024⟩,
      ⟨131683, 961433752110597736697655837327360⟩,
      ⟨7172436928305, -2141299548273022252140712345731072⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 425, 424, 256, 330, 330, 330, 330, 330][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 4850, 33990, 57611, 33825, 4835, 256, 5193, 5193][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 1955, 23705, 131683, 131094, 23835, 1956, 256, 6289][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 0, y := 1, z := 7 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }]
  referenceNumerators := [3, 317, 2283, 606, 27, 1, 0, 106, 3453, 6083, 635, 8, 0, 0, 8, 628, 6069, 3447, 105, 0, 1, 26, 601, 2296, 321, 3]
  marginalXNumerators := [3237, 10285, 10257, 3248, 0, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 33)
    1 1 33

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7.Parent3
