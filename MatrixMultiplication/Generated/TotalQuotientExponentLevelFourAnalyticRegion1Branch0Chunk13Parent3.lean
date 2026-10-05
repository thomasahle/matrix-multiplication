import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 13, parent 57;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 57

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 2660164784578939399040831676481536
  terms := [⟨3, -1901475900342344102245054808064⟩,
      ⟨5, -792281625142643375935439503360⟩,
      ⟨7, -5545971375998503631548076523520⟩,
      ⟨17, -10775030101939949912721977245696⟩,
      ⟨25, -1980704062856608439838598758400⟩,
      ⟨33, -2614529362970723140586950361088⟩,
      ⟨53, -4199092613256009892457829367808⟩,
      ⟨97, 435992578315996649777272358699008⟩,
      ⟨137, -43417033057816857001262084784128⟩,
      ⟨145, -45952334258273315804255491194880⟩,
      ⟨271, 432823451815426076273530600685568⟩,
      ⟨273, -43258576732788328326074996883456⟩,
      ⟨329, 110760971194941543955774442569728⟩,
      ⟨387, 434883384040796949050962743394304⟩,
      ⟨397, -62907161036325884049273896566784⟩,
      ⟨399, -63224073686382941399648072368128⟩,
      ⟨403, 950737950171172051122527404032⟩,
      ⟨543, 432506539165369018923156424884224⟩,
      ⟨573, -45397737120673465441100683542528⟩,
      ⟨699, -110760971194941543955774442569728⟩,
      ⟨1135, -89923964453690023168672383631360⟩,
      ⟨1137, -90082420778718551843859471532032⟩,
      ⟨1323, 111474024657569922994116338122752⟩,
      ⟨1407, -111474024657569922994116338122752⟩,
      ⟨1859, -294570308228034807172796407349248⟩,
      ⟨1981, 10141204801825835211973625643008⟩,
      ⟨1987, 10378889289368628224754257494016⟩,
      ⟨2017, 180640210532522689713280206766080⟩,
      ⟨3713, -294174167415463485484828687597568⟩,
      ⟨5489, -434883384040796949050962743394304⟩,
      ⟨5503, -435992578315996649777272358699008⟩,
      ⟨6931, 2196521577545464495443412479115264⟩,
      ⟨8107, 181274035832636804414028558368768⟩,
      ⟨50465, 714875710366207118106547063881728⟩,
      ⟨9835528509, -1098260788772732247721706239557632⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 2632, 6208, 6192, 2646, 256, 1612, 1612, 1612][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 543, 542, 256, 373, 373, 373, 373, 373][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 403, 1987, 16214, 50465, 16136, 1981, 403, 256][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 0, y := 1, z := 7 }, { x := 0, y := 0, z := 8 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }]
  referenceNumerators := [24, 7, 1, 0, 794, 546, 53, 5, 580, 3718, 1137, 68, 68, 1135, 3713, 573, 5, 56, 548, 798, 0, 1, 7, 25]
  marginalXNumerators := [32, 1398, 5503, 5489, 1407, 33, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 57)
    1 1 57

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13.Parent3
