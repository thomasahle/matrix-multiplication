import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 17, parent 72;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17.Parent2

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 72

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 28205859680378218298002394671218688
  terms := [⟨7, -1109194275199700726309615304704⟩,
      ⟨13, -4119864450741745554864285417472⟩,
      ⟨15, -2376844875427930127806318510080⟩,
      ⟨17, 6100568513598353994702884175872⟩,
      ⟨19, -6021340351084089657109340225536⟩,
      ⟨27, -12834962327310822690154119954432⟩,
      ⟨31, -2456073037942194465399862460416⟩,
      ⟨39, -6179796676112618332296428126208⟩,
      ⟨57, -36128042106504537942656041353216⟩,
      ⟨77, -6100568513598353994702884175872⟩,
      ⟨231, 1678686307352232784932009219719168⟩,
      ⟨257, 86358697140548127976962905866240⟩,
      ⟨401, -127081972672879997500044496338944⟩,
      ⟨453, -35890357618961744929875409502208⟩,
      ⟨463, 672488643421075697494001050451968⟩,
      ⟨541, -85724871840434013276214554263552⟩,
      ⟨545, -43179348570274063988481452933120⟩,
      ⟨549, -43496261220331121338855628734464⟩,
      ⟨671, 273257932511697700360133084708864⟩,
      ⟨821, -260185285696844084657198332903424⟩,
      ⟨933, 1988230738295463551909985433681920⟩,
      ⟨937, -148473576551731368650301362929664⟩,
      ⟨1081, -85645643677919748938621010313216⟩,
      ⟨1087, 6021340351084089657109340225536⟩,
      ⟨1227, -388851821620009368909113708249088⟩,
      ⟨1597, -126527375535280147136889688686592⟩,
      ⟨1641, -260026829371815555982011245002752⟩,
      ⟨1871, -148235892064188575637520731078656⟩,
      ⟨2201, 260026829371815555982011245002752⟩,
      ⟨2463, -390277928545266126985797499355136⟩,
      ⟨2687, 273178704349183436022539540758528⟩,
      ⟨3745, 1314078303461588303326519960272896⟩,
      ⟨4753, -753142912860596793164228791894016⟩,
      ⟨5041, 6390226675750504412944880858300416⟩,
      ⟨8407, -1332142324514840572297847980949504⟩,
      ⟨9505, -753063684698082528826635247943680⟩,
      ⟨16791, -1330320076777012492533196470091776⟩,
      ⟨17595, 260185285696844084657198332903424⟩,
      ⟨109761, 1332142324514840572297847980949504⟩,
      ⟨110175, 1330320076777012492533196470091776⟩,
      ⟨6294676066859, -3195113337875252206472440429150208⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 2176, 35190, 110175, 109761, 35216, 2174, 256, 6814][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 2684, 7490, 7464, 2687, 256, 1726, 1726, 1726][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[257, 926, 1848, 933, 256, 637, 637, 637, 637][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }]
  referenceNumerators := [1, 1, 7, 39, 31, 54, 1081, 1604, 545, 54, 1871, 9505, 4908, 453, 456, 4926, 9506, 1874, 52, 549, 1597, 1082, 54, 30, 39, 7, 1, 1]
  marginalXNumerators := [2, 77, 3284, 16791, 16814, 3282, 76, 2, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 72)
    1 1 72

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17.Parent2
