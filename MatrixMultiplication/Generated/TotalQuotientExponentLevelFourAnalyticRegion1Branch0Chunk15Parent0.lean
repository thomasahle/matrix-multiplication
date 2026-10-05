import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 15, parent 62;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15.Parent0

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 62

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 1113234911487928207526886046171136
  terms := [⟨3, -475368975085586025561263702016⟩,
      ⟨7, -2218388550399401452619230609408⟩,
      ⟨9, -1426106925256758076683791106048⟩,
      ⟨27, -2139160387885137115025686659072⟩,
      ⟨57, -72256084213009075885312082706432⟩,
      ⟨63, -19965496953594613073573075484672⟩,
      ⟨155, 860893213879996292291448564350976⟩,
      ⟨193, -30582070730506034311107964829696⟩,
      ⟨197, -124863584122480596047425265729536⟩,
      ⟨205, -519736746093574054613648314204160⟩,
      ⟨257, 200684935648631567124446826201088⟩,
      ⟨261, -41357100832445984223829942075392⟩,
      ⟨265, -41990926132560098924578293678080⟩,
      ⟨377, -29869017267877655272766069276672⟩,
      ⟨533, -42228610620102891937358925529088⟩,
      ⟨619, 859942475929825120240326036946944⟩,
      ⟨907, -71859943400437754197344362954752⟩,
      ⟨1011, -320398689207684981228291735158784⟩,
      ⟨1591, -126052006560194561111328424984576⟩,
      ⟨2297, 2931442013027780490961126162432⟩,
      ⟨2299, 3010670175542044828554670112768⟩,
      ⟨3281, -519895202418602583288835402104832⟩,
      ⟨4037, -319844092070085130865136927506432⟩,
      ⟨5235, 40564819207303340847894502572032⟩,
      ⟨5269, 41357100832445984223829942075392⟩,
      ⟨5769, -457067269544790963577155049488384⟩,
      ⟨5779, -457859551169933606953090488991744⟩,
      ⟨8945, 519895202418602583288835402104832⟩,
      ⟨12611, -999146357467387561392182757687296⟩,
      ⟨17273, 932436244630376989138418751504384⟩,
      ⟨25163, 999146357467387561392182757687296⟩,
      ⟨26775, 4242668102638855278134278540492800⟩,
      ⟨30617, 124071302497337952671489826226176⟩,
      ⟨30895, 124705127797452067372238177828864⟩,
      ⟨35731, 519736746093574054613648314204160⟩,
      ⟨138583, 934100036043176540227883174461440⟩,
      ⟨10044891037643, -2121334051319427639067139270246400⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 5269, 35731, 50326, 35780, 5235, 256, 5293, 5293][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 2297, 30617, 138184, 138583, 30895, 2299, 256, 7074][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[257, 619, 620, 256, 399, 399, 399, 399, 399][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 7, z := 1 }, { x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }]
  referenceNumerators := [0, 1, 3, 1, 9, 126, 386, 28, 912, 4044, 1576, 533, 5769, 5779, 530, 1591, 4037, 907, 27, 377, 126, 9, 0, 3, 1, 0]
  marginalXNumerators := [4, 522, 6560, 12611, 6562, 512, 4, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 62)
    1 1 62

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15.Parent0
