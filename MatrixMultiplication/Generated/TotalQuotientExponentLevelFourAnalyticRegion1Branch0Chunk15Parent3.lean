import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 15, parent 65;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 65

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 4596738760915102602839826454544384
  terms := [⟨3, -950737950171172051122527404032⟩,
      ⟨7, -8873554201597605810476922437632⟩,
      ⟨11, -1743019575313815427057966907392⟩,
      ⟨23, -14577981902624638117212086861824⟩,
      ⟨29, -9190466851654663160851098238976⟩,
      ⟨47, -14894894552681695467586262663168⟩,
      ⟨161, -408183493273489867281938432131072⟩,
      ⟨193, -61164141461012068622215929659392⟩,
      ⟨227, -143878343125904037069875813810176⟩,
      ⟨259, 119555297234024885428657821057024⟩,
      ⟨273, -346068613862306626608599975067648⟩,
      ⟨333, -52765956234500048837300270923776⟩,
      ⟨357, 93647688091860447035568949297152⟩,
      ⟨379, -30027473592906183947953157177344⟩,
      ⟨401, -31770493168219999375011124084736⟩,
      ⟨579, -91746212191518102933323894489088⟩,
      ⟨591, -93647688091860447035568949297152⟩,
      ⟨653, -51735990121814612448584199569408⟩,
      ⟨771, 2085364465537951629799670316793856⟩,
      ⟨939, 984647603727277187612564214775808⟩,
      ⟨945, 986865992277676589065183445385216⟩,
      ⟨1091, -345751701212249569258225799266304⟩,
      ⟨1177, 54588203972328128601951781781504⟩,
      ⟨1973, -1250537317125148304576497712103424⟩,
      ⟨2341, 54033606834728278238796974129152⟩,
      ⟨3111, -1971830508655010834028121835962368⟩,
      ⟨3513, -556657069825221235932239795060736⟩,
      ⟨3515, -556973982475278293282613970862080⟩,
      ⟨5157, -408579634086061188969906151882752⟩,
      ⟨5631, 91746212191518102933323894489088⟩,
      ⟨8197, 879274147583305618613150760828928⟩,
      ⟨13477, -1067757946204740477748191818678272⟩,
      ⟨13485, -1068391771504854592448940170280960⟩,
      ⟨13553, 8590234292446596539242409271230464⟩,
      ⟨23005, 1971830508655010834028121835962368⟩,
      ⟨32517, 878957234933248561262776585027584⟩,
      ⟨32893, 1067757946204740477748191818678272⟩,
      ⟨33057, 1068391771504854592448940170280960⟩,
      ⟨79095, 2426520933324373867477470566940672⟩,
      ⟨9154799272753, -4295117146223298269621204635615232⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 5712, 32893, 46010, 33057, 5631, 256, 5219, 5219][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 939, 1542, 945, 259, 619, 619, 619, 619][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 4708, 32517, 79095, 32788, 4682, 256, 5328, 5328][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }]
  referenceNumerators := [8, 3, 0, 401, 666, 112, 3, 908, 7030, 5152, 379, 8, 184, 4368, 15784, 4364, 188, 8, 386, 5157, 7026, 908, 3, 116, 653, 386, 0, 3, 8]
  marginalXNumerators := [11, 1182, 13477, 24888, 13485, 1158, 11, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 65)
    1 1 65

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15.Parent3
