import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 15, parent 64;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15.Parent2

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 64

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := -4257879909841594030952238978957312
  terms := [⟨3, -950737950171172051122527404032⟩,
      ⟨5, -1584563250285286751870879006720⟩,
      ⟨11, -1743019575313815427057966907392⟩,
      ⟨21, -1663791412799551089464422957056⟩,
      ⟨29, -4595233425827331580425549119488⟩,
      ⟨55, -4357548938284538567644917268480⟩,
      ⟨57, -4516005263313067242832005169152⟩,
      ⟨59, -4674461588341595918019093069824⟩,
      ⟨111, -8794326039083341472883378487296⟩,
      ⟨113, -8952782364111870148070466387968⟩,
      ⟨115, -9111238689140398823257554288640⟩,
      ⟨119, -9428151339197456173631730089984⟩,
      ⟨129, 31691265005705735037417580134400⟩,
      ⟨163, -103313523918600696221981311238144⟩,
      ⟨283, -44843139983073615077945875890176⟩,
      ⟨321, -813831685346523275760883457851392⟩,
      ⟨325, -102996611268543638871607135436800⟩,
      ⟨363, -57519645985355909092912907943936⟩,
      ⟨573, -45397737120673465441100683542528⟩,
      ⟨687, 474972834273014703873295982264320⟩,
      ⟨695, -110127145894827429255026090967040⟩,
      ⟨709, -56172767222613415353822660788224⟩,
      ⟨961, -304553056704832113709582945091584⟩,
      ⟨1223, -193792085509890569753808502521856⟩,
      ⟨1227, -194425910810004684454556854124544⟩,
      ⟨1367, 474180552647872060497360542760960⟩,
      ⟨1413, -111949393632655509019677601824768⟩,
      ⟨1521, 110127145894827429255026090967040⟩,
      ⟨1801, -1141519365505520576047781236441088⟩,
      ⟨1903, 2203889796659291078839612066496512⟩,
      ⟨2099, -1330399304939526756870790014042112⟩,
      ⟨2227, 352486095025962037953677035044864⟩,
      ⟨2237, 352248410538419244940896403193856⟩,
      ⟨3087, 111949393632655509019677601824768⟩,
      ⟨3851, -305107653842431964072737752743936⟩,
      ⟨7215, -1143262385080834391474839203348480⟩,
      ⟨7669, 2199928388533577861959934868979712⟩,
      ⟨8425, -1334994538365354088451215563161600⟩,
      ⟨9115, 2324554288168515664994579502858240⟩,
      ⟨9191, 2324554288168515664994579502858240⟩,
      ⟨10317, -817396952659665170952592935616512⟩,
      ⟨12351, 2494498696761612669132731276328960⟩,
      ⟨31485, -2494498696761612669132731276328960⟩,
      ⟨33981, 10769008761588865823064867905470464⟩,
      ⟨34757, 1330399304939526756870790014042112⟩,
      ⟨34877, 1334994538365354088451215563161600⟩,
      ⟨3997250738227, -5384504380794432911532433952735232⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 6084, 34877, 49404, 34757, 6174, 256, 5475, 5475][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[258, 2748, 7669, 7612, 2734, 256, 1753, 1753, 1753][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 2237, 9191, 9115, 2227, 258, 1738, 1738, 1738][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }]
  referenceNumerators := [3, 10, 3, 58, 709, 566, 57, 113, 3851, 10317, 2454, 115, 21, 1304, 14430, 14408, 1300, 22, 111, 2446, 10272, 3844, 119, 55, 573, 726, 59, 3, 10, 3]
  marginalXNumerators := [16, 1390, 16850, 31485, 16792, 1413, 16, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 64)
    1 1 64

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15.Parent2
