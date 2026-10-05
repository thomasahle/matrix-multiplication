import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 7, parent 31;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7.Parent1

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 31

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 4301930768199525002654249415344128
  terms := [⟨5, -1188422437713965063903159255040⟩,
      ⟨7, -4436777100798802905238461218816⟩,
      ⟨21, -6655165651198204357857691828224⟩,
      ⟨23, -3644495475656159529303021715456⟩,
      ⟨25, -126765060022822940149670320537600⟩,
      ⟨31, 442013918667080739434381698924544⟩,
      ⟨55, -4357548938284538567644917268480⟩,
      ⟨83, -6575937488683940020264147877888⟩,
      ⟨109, -34543478856219251190785162346496⟩,
      ⟨147, -46586159558387430505003842797568⟩,
      ⟨187, 396140812571321687967719751680⟩,
      ⟨375, 475368975085586025561263702016⟩,
      ⟨439, -34781163343762044203565794197504⟩,
      ⟨497, 441776234179537946421601067073536⟩,
      ⟨587, -46506931395873166167410298847232⟩,
      ⟨697, -441776234179537946421601067073536⟩,
      ⟨901, -142769148850704336343566198505472⟩,
      ⟨1021, 11408855402054064613470328848384⟩,
      ⟨1221, 86121012653005334964182274015232⟩,
      ⟨1321, -104660402681343189961071558393856⟩,
      ⟨1323, -104818859006371718636258646294528⟩,
      ⟨1599, -126685831860308675812076776587264⟩,
      ⟨1877, -297422522078548323326163989561344⟩,
      ⟨2041, 11408855402054064613470328848384⟩,
      ⟨2181, 212806844513314010776259050602496⟩,
      ⟨2435, 85804100002948277613808098213888⟩,
      ⟨3743, 480439577486498943167250514837504⟩,
      ⟨3759, -297818662891119645014131709313024⟩,
      ⟨5579, -442013918667080739434381698924544⟩,
      ⟨7177, 2274482089459500603635459726245888⟩,
      ⟨7493, 480281121161470414492063426936832⟩,
      ⟨17407, 212410703700742689088291330850816⟩,
      ⟨22615, 688334275923928565012709840519168⟩,
      ⟨323828727115, -1137241044729750301817729863122944⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 497, 496, 256, 357, 357, 357, 357, 357][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 375, 2041, 17448, 45230, 17407, 2042, 374, 256][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 2435, 7486, 7493, 2442, 256, 1672, 1672, 1672][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 8, z := 0 }, { x := 0, y := 7, z := 1 }, { x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }]
  referenceNumerators := [0, 4, 83, 901, 588, 23, 1, 56, 1321, 3754, 439, 5, 5, 436, 3759, 1323, 55, 1, 23, 587, 901, 84, 5, 0]
  marginalXNumerators := [1599, 5576, 5579, 1600, 0, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 31)
    1 1 31

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7.Parent1
