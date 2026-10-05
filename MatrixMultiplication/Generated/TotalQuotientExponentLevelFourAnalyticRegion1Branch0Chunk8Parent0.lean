import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 8, parent 34;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk8.Parent0

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 34

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 8168740467870710263244755455442944
  terms := [⟨3, -950737950171172051122527404032⟩,
      ⟨5, -792281625142643375935439503360⟩,
      ⟨11, -1743019575313815427057966907392⟩,
      ⟨23, -1822247737828079764651510857728⟩,
      ⟨25, -3961408125713216879677197516800⟩,
      ⟨35, -5545971375998503631548076523520⟩,
      ⟨51, -4040636288227481217270741467136⟩,
      ⟨57, -36128042106504537942656041353216⟩,
      ⟨71, -5625199538512767969141620473856⟩,
      ⟨129, 126685831860308675812076776587264⟩,
      ⟨185, 950737950171172051122527404032⟩,
      ⟨225, -35652673131418951917094777651200⟩,
      ⟨243, 429892009802398295782569474523136⟩,
      ⟨361, -57202733335298851742538732142592⟩,
      ⟨363, -57519645985355909092912907943936⟩,
      ⟨383, -60688772485926482596654665957376⟩,
      ⟨479, 10141204801825835211973625643008⟩,
      ⟨487, 430129694289941088795350106374144⟩,
      ⟨775, -61401825948554861634996561510400⟩,
      ⟨793, -125655865747623239423360705232896⟩,
      ⟨1161, -91983896679060895946104526340096⟩,
      ⟨1165, -92300809329117953296478702141440⟩,
      ⟨1599, -126685831860308675812076776587264⟩,
      ⟨1755, 2224726803400542599626714125434880⟩,
      ⟨1875, -297105609428491265975789813760000⟩,
      ⟨1879, -297739434728605380676538165362688⟩,
      ⟨1913, 9982748476797306536786537742336⟩,
      ⟨2533, 100778222718144237418987904827392⟩,
      ⟨2559, 101887416993343938145297520132096⟩,
      ⟨2713, -429892009802398295782569474523136⟩,
      ⟨3453, 452155123468906574646355324567552⟩,
      ⟨5429, -430129694289941088795350106374144⟩,
      ⟨6917, 452868176931534953684697220120576⟩,
      ⟨8005, 187057691696178101058357266743296⟩,
      ⟨16023, 187295376183720894071137898594304⟩,
      ⟨24329, 716935642591577990883979206590464⟩,
      ⟨609920256803, -1112363401700271299813357062717440⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 486, 487, 258, 354, 354, 354, 354, 354][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 2559, 6906, 6917, 2533, 256, 1652, 1652, 1652][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 370, 1916, 16023, 48658, 16010, 1913, 370, 256][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 0, y := 1, z := 7 }, { x := 0, y := 0, z := 8 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }]
  referenceNumerators := [23, 766, 722, 70, 5, 0, 6, 450, 3758, 1161, 50, 1, 1, 51, 1165, 3750, 456, 6, 0, 5, 71, 726, 775, 22]
  marginalXNumerators := [1586, 5426, 5429, 1599, 0, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 34)
    1 1 34

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk8.Parent0
