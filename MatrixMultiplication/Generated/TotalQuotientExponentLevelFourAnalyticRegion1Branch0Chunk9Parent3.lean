import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 9, parent 41;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk9.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 41

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 732939731419459387077875084558336
  terms := [⟨3, -2376844875427930127806318510080⟩,
      ⟨25, -7922816251426433759354395033600⟩,
      ⟨29, -2297616712913665790212774559744⟩,
      ⟨31, 64967093261696756826706039275520⟩,
      ⟨51, -8081272576454962434541482934272⟩,
      ⟨63, -4991374238398653268393268871168⟩,
      ⟨69, -5466743213484239293954532573184⟩,
      ⟨71, -5625199538512767969141620473856⟩,
      ⟨97, -7685131763883640746573763182592⟩,
      ⟨105, -8318957063997755447322114785280⟩,
      ⟨129, 32245862143305585400572387786752⟩,
      ⟨199, -63065617361354412724460984467456⟩,
      ⟨225, -71305346262837903834189555302400⟩,
      ⟨245, 71305346262837903834189555302400⟩,
      ⟨253, -20044725116108877411166619435008⟩,
      ⟨257, 8318957063997755447322114785280⟩,
      ⟨259, -20520094091194463436727883137024⟩,
      ⟨269, -42624751432674213625326645280768⟩,
      ⟨271, -42941664082731270975700821082112⟩,
      ⟨277, 475368975085586025561263702016⟩,
      ⟨395, -62590248386268826698899720765440⟩,
      ⟨479, 15687176177824338843521702166528⟩,
      ⟨559, 116227714408425783249728975142912⟩,
      ⟨561, 116623855220997104937696694894592⟩,
      ⟨863, -136747808499620246686456858279936⟩,
      ⟨913, -72335312375523340222905626656768⟩,
      ⟨959, 15766404340338603181115246116864⟩,
      ⟨1485, 136747808499620246686456858279936⟩,
      ⟨1873, 593577393556868417250831275917312⟩,
      ⟨2437, 130488783660993364016566886203392⟩,
      ⟨4903, 131201837123621743054908781756416⟩,
      ⟨9478194165, -296788696778434208625415637958656⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 992, 1485, 980, 257, 624, 624, 624, 624][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[759, 277, 256, 959, 4903, 4874, 958, 256, 277][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 559, 561, 258, 379, 379, 379, 379, 379][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 8, z := 0 }, { x := 0, y := 7, z := 1 }, { x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }]
  referenceNumerators := [3, 8, 29, 62, 12, 100, 542, 259, 69, 790, 796, 71, 253, 538, 97, 12, 63, 31, 8, 3]
  marginalXNumerators := [102, 913, 1726, 900, 105, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 41)
    1 1 41

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk9.Parent3
