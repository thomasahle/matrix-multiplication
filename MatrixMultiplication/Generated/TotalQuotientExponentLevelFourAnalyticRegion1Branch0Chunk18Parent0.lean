import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 18, parent 74;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18.Parent0

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 74

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := -9500248967085436720841855084789760
  terms := [⟨3, -15687176177824338843521702166528⟩,
      ⟨9, -1426106925256758076683791106048⟩,
      ⟨21, -3327582825599102178928845914112⟩,
      ⟨33, -2614529362970723140586950361088⟩,
      ⟨39, -98876746817801893316742850019328⟩,
      ⟨41, -3248354663084837841335301963776⟩,
      ⟨53, -8398185226512019784915658735616⟩,
      ⟨111, -8794326039083341472883378487296⟩,
      ⟨171, -108384126319513613827968124059648⟩,
      ⟨189, -14974122715195959805179806613504⟩,
      ⟨257, 224453384402910868402510011301888⟩,
      ⟨265, 843225333639315345008088263426048⟩,
      ⟨465, -73682191138265833961995873812480⟩,
      ⟨491, 3248354663084837841335301963776⟩,
      ⟨529, 840452347951316093192314225164288⟩,
      ⟨695, -881017167158619434040208727736320⟩,
      ⟨937, -74236788275865684325150681464832⟩,
      ⟨1147, -181749404807722390439589822070784⟩,
      ⟨1235, -97846780705116456928026778664960⟩,
      ⟨1359, -107671072856885234789626228506624⟩,
      ⟨1647, -521955134643973456066267544813568⟩,
      ⟨1967, 3327582825599102178928845914112⟩,
      ⟨2279, -180560982370008425375686662815744⟩,
      ⟨2333, 24402274054393415978811536703488⟩,
      ⟨2975, -471407566959872808681586504499200⟩,
      ⟨4675, 24560730379421944653998624604160⟩,
      ⟨6611, -523777382381801535830919055671296⟩,
      ⟨11137, -882364045921361927779298974892032⟩,
      ⟨18563, 1242456044548693342141956229169152⟩,
      ⟨22805, 881017167158619434040208727736320⟩,
      ⟨26915, 4264851988142849292660470846586880⟩,
      ⟨29105, 180560982370008425375686662815744⟩,
      ⟨29239, 181749404807722390439589822070784⟩,
      ⟨30983, 419592348675543931895408760979456⟩,
      ⟨31131, 420939227438286425634499008135168⟩,
      ⟨90743, 882364045921361927779298974892032⟩,
      ⟨439843118517, -2132425994071424646330235423293440⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 1964, 29105, 91220, 90743, 29239, 1967, 256, 6046][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[257, 530, 529, 256, 368, 368, 368, 368, 368][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 4666, 31131, 74252, 30983, 4675, 256, 5197, 5197][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }]
  referenceNumerators := [1, 0, 32, 9, 0, 1235, 930, 111, 3, 1368, 6588, 2975, 189, 192, 2975, 6611, 1359, 3, 106, 937, 1248, 0, 9, 33, 0, 1]
  marginalXNumerators := [1, 41, 2279, 11120, 11137, 2294, 42, 1, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 74)
    1 1 74

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18.Parent0
