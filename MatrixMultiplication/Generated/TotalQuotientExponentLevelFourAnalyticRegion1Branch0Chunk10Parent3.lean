import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 10, parent 45;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10.Parent3

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 45

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 21127853325841385170407958780051456
  terms := [⟨3, -4753689750855860255612637020160⟩,
      ⟨27, -4278320775770274230051373318144⟩,
      ⟨33, -13072646814853615702934751805440⟩,
      ⟨49, -3882179963198952542083653566464⟩,
      ⟨67, -42466295107645684950139557380096⟩,
      ⟨209, -33117371930962493114101371240448⟩,
      ⟨409, -32404318468334114075759475687424⟩,
      ⟨463, -73365278488208776611621698011136⟩,
      ⟨471, -69403870362495559731944500494336⟩,
      ⟨507, -80337356789464038319853565640704⟩,
      ⟨547, 1429909877057442764888281215664128⟩,
      ⟨689, 305186882004946228410331296694272⟩,
      ⟨719, -113930097695512117459516200583168⟩,
      ⟨831, 800283669556584074032387442343936⟩,
      ⟨833, 801234407506755246083509969747968⟩,
      ⟨941, 5149830563427181943580356771840⟩,
      ⟨1005, -79624303326835659281511670087680⟩,
      ⟨1165, -184601618658235906592957404282880⟩,
      ⟨1167, -184918531308292963943331580084224⟩,
      ⟨1445, -114484694833111967822671008235520⟩,
      ⟨1671, -529561038245342832475247764045824⟩,
      ⟨1819, 1336975242428210696891054161920000⟩,
      ⟨2729, 303443862429632412983273329786880⟩,
      ⟨6683, -529481810082828568137654220095488⟩,
      ⟨7263, 1338322121190953190630144409075712⟩,
      ⟨8741, -692533368537184574905167669886976⟩,
      ⟨8759, -693959475462441332981851460993024⟩,
      ⟨10101, -800283669556584074032387442343936⟩,
      ⟨10113, -801234407506755246083509969747968⟩,
      ⟨10423, 6606361103089417525900068754817024⟩,
      ⟨11469, 158377096866014410849494356721664⟩,
      ⟨18595, -1473247681952745357551949756497920⟩,
      ⟨23213, 160595485416413812302113587331072⟩,
      ⟨34045, 1485211134492399272528574892998656⟩,
      ⟨137045, 1488301032830455581694723107061760⟩,
      ⟨5189033793941, -3303180551544708762950034377408512⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 831, 1094, 833, 256, 549, 549, 549, 549][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 2729, 7263, 7276, 2756, 256, 1722, 1722, 1722][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 1882, 23213, 136180, 137045, 22938, 1884, 256, 6244][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 0, y := 1, z := 7 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }]
  referenceNumerators := [66, 942, 409, 27, 1, 48, 2330, 6684, 1005, 33, 1, 6, 547, 8741, 8759, 536, 6, 1, 32, 1014, 6683, 2334, 49, 1, 27, 418, 926, 66]
  marginalXNumerators := [1445, 10101, 18595, 10113, 1438, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 45)
    1 1 45

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10.Parent3
