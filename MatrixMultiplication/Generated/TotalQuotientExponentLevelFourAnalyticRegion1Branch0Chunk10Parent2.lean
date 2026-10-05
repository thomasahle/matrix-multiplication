import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 10, parent 44;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10.Parent2

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 44

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 9482422630519727244883307695964160
  terms := [⟨3, -1901475900342344102245054808064⟩,
      ⟨7, -1109194275199700726309615304704⟩,
      ⟨59, -18697846353366383672076372279296⟩,
      ⟨95, -7526675438855112071386675281920⟩,
      ⟨97, -7685131763883640746573763182592⟩,
      ⟨117, -18539390028337854996889284378624⟩,
      ⟨225, 1952815749651587393005671287881728⟩,
      ⟨229, -36286498431533066617843129253888⟩,
      ⟨257, 161466995204070720015642570784768⟩,
      ⟨377, -29869017267877655272766069276672⟩,
      ⟨383, -30344386242963241298327332978688⟩,
      ⟨387, -30661298893020298648701508780032⟩,
      ⟨399, -31612036843191470699824036184064⟩,
      ⟨453, -35890357618961744929875409502208⟩,
      ⟨695, -110127145894827429255026090967040⟩,
      ⟨719, 1071402441680396637277494840393728⟩,
      ⟨721, -456988041382276699239561505538048⟩,
      ⟨723, 1073145461255710452704552807301120⟩,
      ⟨1019, -161466995204070720015642570784768⟩,
      ⟨1171, 56489679872670472704196836589568⟩,
      ⟨1385, -109731005082256107567058371215360⟩,
      ⟨1733, -549209622548880388198446663729152⟩,
      ⟨2019, -159961660116299697601365235728384⟩,
      ⟨2609, 74870613575979799025899033067520⟩,
      ⟨2613, 75266754388551120713866752819200⟩,
      ⟨2883, -456829585057248170564374417637376⟩,
      ⟨3081, -1952815749651587393005671287881728⟩,
      ⟨3973, -314773489669172213259150114684928⟩,
      ⟨3977, -315090402319229270609524290486272⟩,
      ⟨4695, 56648136197699001379383924490240⟩,
      ⟨6919, -548179656436194951809730592374784⟩,
      ⟨8191, 2258794913281676264791938024079360⟩,
      ⟨8253, -1307740050460447156319036444246016⟩,
      ⟨8581, 919046685165466316085109823897600⟩,
      ⟨13523, -1071402441680396637277494840393728⟩,
      ⟨13545, -1073145461255710452704552807301120⟩,
      ⟨17115, 917779034565238086683613120692224⟩,
      ⟨20079, 2467402665181734265675739245314048⟩,
      ⟨35939, 1004375416193329007673356658409472⟩,
      ⟨36051, 1003900047218243421647795394707456⟩,
      ⟨55773, 8837584615816129801209453484179456⟩,
      ⟨15929472825091, -4418792307908064900604726742089728⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[257, 719, 900, 723, 256, 499, 499, 499, 499][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 5218, 35939, 65528, 36051, 5226, 256, 5497, 5497][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 4695, 34230, 80316, 34324, 4684, 256, 5412, 5412][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }]
  referenceNumerators := [7, 399, 1390, 236, 6, 3, 453, 6919, 5768, 377, 3, 0, 95, 3973, 16506, 3977, 97, 0, 3, 383, 5766, 6932, 458, 3, 6, 234, 1385, 387, 7]
  marginalXNumerators := [2038, 13523, 24648, 13545, 2019, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 44)
    1 1 44

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10.Parent2
