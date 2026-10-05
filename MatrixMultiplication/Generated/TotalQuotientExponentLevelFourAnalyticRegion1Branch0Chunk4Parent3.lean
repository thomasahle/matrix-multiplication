import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 4, parent 21;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk4.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 21

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := -1279534824605369052135734797926400
  terms := [⟨13, -4119864450741745554864285417472⟩,
      ⟨25, -3961408125713216879677197516800⟩,
      ⟨41, -6496709326169675682670603927552⟩,
      ⟨55, -139441566025105234164637352591360⟩,
      ⟨129, 140075391325219348865385704194048⟩,
      ⟨133, -84298764915177255199530763157504⟩,
      ⟨173, 263275184034900393823346546966528⟩,
      ⟨221, -140075391325219348865385704194048⟩,
      ⟨241, -38187974331875410720088184061952⟩,
      ⟨293, -185710812933435607319267019587584⟩,
      ⟨301, -47695353833587131231313458102272⟩,
      ⟨367, 158456325028528675187087900672⟩,
      ⟨481, -38108746169361146382494640111616⟩,
      ⟨609, -48249950971186981594468265754624⟩,
      ⟨1033, 7764359926397905084167307132928⟩,
      ⟨1067, -84536449402720048212311395008512⟩,
      ⟨1163, 4832917913370124593206180970496⟩,
      ⟨2077, 90557789753804137869420735234048⟩,
      ⟨3323, -263275184034900393823346546966528⟩,
      ⟨4647, 4674461588341595918019093069824⟩,
      ⟨6851, 1085584282770449953706739207503872⟩,
      ⟨8237, 89765508128661494493485295730688⟩,
      ⟨16825, 125893550235166032436141337083904⟩,
      ⟨23523, 354546027251332910731109177753600⟩,
      ⟨33639, 125735093910137503760954249183232⟩,
      ⟨57717, 281656117738209720145048743444480⟩,
      ⟨339036971423, -542792141385224976853369603751936⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[258, 346, 256, 284, 284, 284, 284, 284, 284][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 4652, 33639, 57717, 33650, 4647, 256, 5123, 5123][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 367, 2066, 16474, 47046, 16616, 2066, 367, 256][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 0, y := 1, z := 7 }, { x := 0, y := 0, z := 8 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }]
  referenceNumerators := [0, 50, 1067, 609, 41, 1, 0, 0, 8, 481, 2344, 482, 8, 0, 0, 1, 41, 602, 1064, 52, 0]
  marginalXNumerators := [1768, 3323, 1760, 0, 0, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 21)
    1 1 21

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk4.Parent3
