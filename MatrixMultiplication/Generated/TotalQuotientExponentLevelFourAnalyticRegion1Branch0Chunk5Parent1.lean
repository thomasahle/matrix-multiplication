import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 5, parent 23;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk5.Parent1

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 23

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 242042036481077551348276768276480
  terms := [⟨3, -950737950171172051122527404032⟩,
      ⟨5, -1584563250285286751870879006720⟩,
      ⟨7, -1109194275199700726309615304704⟩,
      ⟨9, -2852213850513516153367582212096⟩,
      ⟨11, -3486039150627630854115933814784⟩,
      ⟨13, -1029966112685436388716071354368⟩,
      ⟨25, -7922816251426433759354395033600⟩,
      ⟨35, -2772985687999251815774038261760⟩,
      ⟨43, -3406810988113366516522389864448⟩,
      ⟨59, -18697846353366383672076372279296⟩,
      ⟨95, -15053350877710224142773350563840⟩,
      ⟨109, -8635869714054812797696290586624⟩,
      ⟨115, 16558685965481246557050685620224⟩,
      ⟨173, 15053350877710224142773350563840⟩,
      ⟨213, 67502394462153215629699445686272⟩,
      ⟨245, 6655165651198204357857691828224⟩,
      ⟨377, 792281625142643375935439503360⟩,
      ⟨491, 6813621976226733033044779728896⟩,
      ⟨945, 15687176177824338843521702166528⟩,
      ⟨1565, 15528719852795810168334614265856⟩,
      ⟨970003961, -33751197231076607814849722843136⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 346, 256, 283, 283, 283, 283, 283, 283][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 945, 1565, 945, 256, 620, 620, 620, 620][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[413, 413, 377, 256, 490, 920, 491, 256, 377][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 0, y := 1, z := 7 }, { x := 0, y := 0, z := 8 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }]
  referenceNumerators := [6, 50, 44, 13, 5, 5, 35, 109, 36, 5, 5, 14, 43, 50, 6]
  marginalXNumerators := [118, 190, 118, 0, 0, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 23)
    1 1 23

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk5.Parent1
