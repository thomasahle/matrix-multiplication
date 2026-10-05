import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 7, parent 32;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7.Parent2

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 32

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 6305214857372698778707008199589888
  terms := [⟨3, -475368975085586025561263702016⟩,
      ⟨9, -713053462628379038341895553024⟩,
      ⟨15, -2376844875427930127806318510080⟩,
      ⟨29, -2297616712913665790212774559744⟩,
      ⟨51, -16162545152909924869082965868544⟩,
      ⟨103, -16321001477938453544270053769216⟩,
      ⟨105, 812405578421266517684199666745344⟩,
      ⟨129, 263195955872386129485753003016192⟩,
      ⟨143, -90637017916318402207014279184384⟩,
      ⟨171, -54192063159756806913984062029824⟩,
      ⟨209, 831341109262175694369056670875648⟩,
      ⟨239, -151484246727273413478856033042432⟩,
      ⟨327, -829043492549262028578843896315904⟩,
      ⟨517, 3010670175542044828554670112768⟩,
      ⟨691, -54746660297356657277138869682176⟩,
      ⟨769, -243705827893877102437741191233536⟩,
      ⟨1151, 25432240167078852367527608057856⟩,
      ⟨1167, -92459265654146481971665790042112⟩,
      ⟨1661, -263195955872386129485753003016192⟩,
      ⟨1923, -152355756514930321192385016496128⟩,
      ⟨2067, 3010670175542044828554670112768⟩,
      ⟨3073, -243468143406334309424960559382528⟩,
      ⟨3307, -262007533434672164421849843761152⟩,
      ⟨3669, 937110706218718585056437844574208⟩,
      ⟨4587, 25194555679536059354746976206848⟩,
      ⟨6593, -522351275456544777754235264565248⟩,
      ⟨6619, -524411207681915650531667407273984⟩,
      ⟨7037, 153702635277672814931475263651840⟩,
      ⟨10493, -831341109262175694369056670875648⟩,
      ⟨13793, 4371176182236992033711006827937792⟩,
      ⟨28275, 154970285877901044332971966857216⟩,
      ⟨31857, 452313579793935103321542412468224⟩,
      ⟨31925, 452313579793935103321542412468224⟩,
      ⟨72489, 1229858766708925312464582741065728⟩,
      ⟨117305, 933624667068090954202321910759424⟩,
      ⟨7213263289911, -2185588091118496016855503413968896⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[258, 420, 418, 256, 328, 328, 328, 328, 328][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 2068, 28148, 117408, 117305, 28275, 2067, 256, 6471][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 4587, 31925, 72489, 31857, 4604, 256, 5194, 5194][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 7, z := 1 }, { x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }]
  referenceNumerators := [1, 29, 1167, 1912, 210, 3, 0, 9, 684, 6593, 3076, 102, 0, 0, 102, 3073, 6619, 691, 8, 0, 3, 206, 1923, 1144, 30, 1]
  marginalXNumerators := [3322, 10464, 10493, 3307, 0, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 32)
    1 1 32

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7.Parent2
