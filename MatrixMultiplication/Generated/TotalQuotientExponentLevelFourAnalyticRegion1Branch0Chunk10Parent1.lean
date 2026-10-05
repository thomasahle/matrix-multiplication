import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 10, parent 43;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10.Parent1

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 43

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 8710502643143249803709408987840512
  terms := [⟨3, -475368975085586025561263702016⟩,
      ⟨5, -396140812571321687967719751680⟩,
      ⟨9, -2852213850513516153367582212096⟩,
      ⟨29, -4595233425827331580425549119488⟩,
      ⟨31, -2456073037942194465399862460416⟩,
      ⟨37, -2931442013027780490961126162432⟩,
      ⟨49, -7764359926397905084167307132928⟩,
      ⟨51, 804641218494868612600032359612416⟩,
      ⟨57, -4516005263313067242832005169152⟩,
      ⟨257, 113850869532997853121922656632832⟩,
      ⟨275, 5704427701027032306735164424192⟩,
      ⟨283, -44843139983073615077945875890176⟩,
      ⟨295, 243388915243820045087367015432192⟩,
      ⟨345, -54667432134842392939545325731840⟩,
      ⟨571, -45239280795644936765913595641856⟩,
      ⟨651, -51577533796786083773397111668736⟩,
      ⟨655, -51894446446843141123771287470080⟩,
      ⟨683, -108225669994485085152781036158976⟩,
      ⟨695, -55063572947413714627513045483520⟩,
      ⟨717, -113613185045455060109142024781824⟩,
      ⟨817, 804561990332354348262438815662080⟩,
      ⟨889, -140867672950361992241321143697408⟩,
      ⟨1059, 1491470159331026155198464865075200⟩,
      ⟨1187, 244498109519019745813676630736896⟩,
      ⟨1361, -107829529181913763464813316407296⟩,
      ⟨1437, -113850869532997853121922656632832⟩,
      ⟨1783, -141263813762933313929288863449088⟩,
      ⟨1869, 209241577200172115584549572837376⟩,
      ⟨2207, 5942112188569825319515796275200⟩,
      ⟨2213, -701327694576267916378051048374272⟩,
      ⟨2539, -804641218494868612600032359612416⟩,
      ⟨3463, -1097468507147589604345770800054272⟩,
      ⟨4095, 1412321224979276081942514458689536⟩,
      ⟨8187, 1410182064591390944827488772030464⟩,
      ⟨8291, 1448449267085780619885170500042752⟩,
      ⟨8825, -699188534188382779263025361715200⟩,
      ⟨10155, -804561990332354348262438815662080⟩,
      ⟨18825, -1491470159331026155198464865075200⟩,
      ⟨29699, 208132382924972414858239957532672⟩,
      ⟨42007, 6656274845473404058584001443528704⟩,
      ⟨132555, 1450509199311151492662602642751488⟩,
      ⟨5468919722387, -3328137422736702029292000721764352⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 817, 1059, 816, 257, 541, 541, 541, 541][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 2207, 29699, 132555, 132656, 29904, 2200, 256, 6872][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 2374, 8187, 8190, 2360, 256, 1706, 1706, 1706][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 7, z := 1 }, { x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }]
  referenceNumerators := [1, 31, 655, 690, 57, 0, 36, 1366, 6926, 1778, 49, 5, 571, 8825, 8852, 566, 6, 49, 1783, 6926, 1361, 37, 0, 58, 695, 651, 32, 1]
  marginalXNumerators := [1434, 10155, 18825, 10156, 1437, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 43)
    1 1 43

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10.Parent1
