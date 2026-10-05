import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 12, parent 52;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk12.Parent2

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 52

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 1010317528381898832992872454684672
  terms := [⟨7, -1109194275199700726309615304704⟩,
      ⟨15, -4753689750855860255612637020160⟩,
      ⟨25, -1980704062856608439838598758400⟩,
      ⟨27, -2139160387885137115025686659072⟩,
      ⟨31, -4912146075884388930799724920832⟩,
      ⟨33, -2614529362970723140586950361088⟩,
      ⟨35, -2772985687999251815774038261760⟩,
      ⟨71, 431635029377712111209627441430528⟩,
      ⟨111, -281418433250666927132268111593472⟩,
      ⟨165, 109968689569798900579839003066368⟩,
      ⟨171, -108384126319513613827968124059648⟩,
      ⟨257, 112900131582826681070800129228800⟩,
      ⟨307, -48646091783758303282435985506304⟩,
      ⟨347, -109968689569798900579839003066368⟩,
      ⟨349, -110602514869913015280587354669056⟩,
      ⟨351, 792281625142643375935439503360⟩,
      ⟨359, -56885820685241794392164556341248⟩,
      ⟨523, 10933486426968478587909065146368⟩,
      ⟨569, 443994622729937347874220297682944⟩,
      ⟨599, -47457669346044338218532826251264⟩,
      ⟨603, -47774581996101395568907002052608⟩,
      ⟨607, -48091494646158452919281177853952⟩,
      ⟨699, -443043884779766175823097770278912⟩,
      ⟨719, -56965048847756058729758100291584⟩,
      ⟨1365, -108146441831970820815187492208640⟩,
      ⟨1589, 443043884779766175823097770278912⟩,
      ⟨1777, -281576889575695455807455199494144⟩,
      ⟨2095, 11091942751997007263096153047040⟩,
      ⟨2263, 206389363349658599431181990625280⟩,
      ⟨2653, 110602514869913015280587354669056⟩,
      ⟨5595, -443281569267308968835878402129920⟩,
      ⟨6353, 443281569267308968835878402129920⟩,
      ⟨14039, 2224568347075514070951527037534208⟩,
      ⟨18103, 206230907024630070755994902724608⟩,
      ⟨23815, 676846192359360236061645967720448⟩,
      ⟨669807078211, -1112284173537757035475763518767104⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 2640, 6356, 6353, 2653, 256, 1627, 1627, 1627][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 351, 2092, 18103, 47630, 18104, 2095, 351, 256][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[257, 569, 568, 256, 382, 382, 382, 382, 382][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 8, z := 0 }, { x := 0, y := 7, z := 1 }, { x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }]
  referenceNumerators := [0, 1, 7, 27, 4, 62, 603, 719, 71, 1368, 3554, 599, 607, 3552, 1365, 71, 718, 614, 60, 4, 25, 7, 1, 0]
  marginalXNumerators := [35, 1388, 5592, 5595, 1396, 33, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 52)
    1 1 52

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk12.Parent2
