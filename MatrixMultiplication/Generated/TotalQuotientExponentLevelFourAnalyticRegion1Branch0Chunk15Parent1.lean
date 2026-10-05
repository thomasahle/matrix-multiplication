import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 15, parent 63;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15.Parent1

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 63

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 1730026156661476075692625699536896
  terms := [⟨3, -1188422437713965063903159255040⟩,
      ⟨7, -1109194275199700726309615304704⟩,
      ⟨11, -1743019575313815427057966907392⟩,
      ⟨95, 92459265654146481971665790042112⟩,
      ⟨97, -30740527055534562986295052730368⟩,
      ⟨101, -16004088827881396193895877967872⟩,
      ⟨103, -16321001477938453544270053769216⟩,
      ⟨127, -10061976639311570874380081692672⟩,
      ⟨133, -10537345614397156899941345394688⟩,
      ⟨187, -29631332780334862259985437425664⟩,
      ⟨197, -62431792061240298023712632864768⟩,
      ⟨239, -37871061681818353369714008260608⟩,
      ⟨257, 110998655682484336968555074420736⟩,
      ⟨293, -92855406466717803659633509793792⟩,
      ⟨399, -63224073686382941399648072368128⟩,
      ⟨461, 899873469837014346387472187916288⟩,
      ⟨469, 900824207787185518438594715320320⟩,
      ⟨487, -38584115144446732408055903813632⟩,
      ⟨557, -353040692163561888316831842697216⟩,
      ⟨647, -51260621146729026423022935867392⟩,
      ⟨663, -52528271746957255824519639072768⟩,
      ⟨1115, -353357604813618945667206018498560⟩,
      ⟨1167, -92459265654146481971665790042112⟩,
      ⟨1335, 64254039799068377788364143722496⟩,
      ⟨1439, -456037303432105527188438978134016⟩,
      ⟨1983, 2287317051786811426325613846200320⟩,
      ⟨2883, -456829585057248170564374417637376⟩,
      ⟨3159, -2002254123060488339664042712891392⟩,
      ⟨3345, -1060072814440856837001618055495680⟩,
      ⟨3987, -1263530735777487655941838919958528⟩,
      ⟨5407, 65759374886839400202641478778880⟩,
      ⟨6105, 92855406466717803659633509793792⟩,
      ⟨6323, -500959671577693406603978397974528⟩,
      ⟨6339, -502227322177921636005475101179904⟩,
      ⟨8897, 1059042848328171400612901984141312⟩,
      ⟨9111, 968247374086824469730700617056256⟩,
      ⟨13367, -1059042848328171400612901984141312⟩,
      ⟨13595, 8616854955051389356673840038543360⟩,
      ⟨35783, 1060072814440856837001618055495680⟩,
      ⟨36689, 971891869562480629260003638771712⟩,
      ⟨48735, 2002254123060488339664042712891392⟩,
      ⟨66179, 2236769484102710778940932805885952⟩,
      ⟨5301152863493, -4308427477525694678336920019271680⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 6080, 35588, 48735, 35783, 6105, 256, 5493, 5493][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 5407, 36444, 66179, 36689, 5340, 256, 5576, 5576][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[257, 922, 1983, 938, 256, 646, 646, 646, 646][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }]
  referenceNumerators := [0, 4, 7, 3, 127, 663, 374, 6, 478, 6339, 5756, 788, 202, 4460, 15948, 4456, 206, 798, 5766, 6323, 487, 6, 388, 647, 133, 4, 7, 4, 0]
  marginalXNumerators := [11, 1167, 13367, 25272, 13380, 1172, 11, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 63)
    1 1 63

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15.Parent1
