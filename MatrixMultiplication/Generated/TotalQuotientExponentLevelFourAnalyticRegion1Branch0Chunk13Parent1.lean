import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 13, parent 55;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13.Parent1

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 55

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 1055319124690000976746005418475520
  terms := [⟨3, -4753689750855860255612637020160⟩,
      ⟨9, -1426106925256758076683791106048⟩,
      ⟨13, -37078780056675709993778568757248⟩,
      ⟨27, -4278320775770274230051373318144⟩,
      ⟨31, -9824292151768777861599449841664⟩,
      ⟨43, -27254487904906932132179118915584⟩,
      ⟨47, -3723723638170423866896565665792⟩,
      ⟨53, -4199092613256009892457829367808⟩,
      ⟨63, -9982748476797306536786537742336⟩,
      ⟨119, -18856302678394912347263460179968⟩,
      ⟨129, 18856302678394912347263460179968⟩,
      ⟨147, -11646539889596857626250960699392⟩,
      ⟨155, -12280365189710972326999312302080⟩,
      ⟨229, -18143249215766533308921564626944⟩,
      ⟨257, 16162545152909924869082965868544⟩,
      ⟨335, -26541434442278553093837223362560⟩,
      ⟨393, -249093342944847077394102179856384⟩,
      ⟨415, -32879687443419700101320739389440⟩,
      ⟨963, -610373764009892456820662593388544⟩,
      ⟨995, 2306173354465206338672877306380288⟩,
      ⟨1605, 610532220334920985495849681289216⟩,
      ⟨2367, 67502394462153215629699445686272⟩,
      ⟨2373, -376016859292698546218959588294656⟩,
      ⟨2739, 476398941198271461949979773370368⟩,
      ⟨2763, 477349679148442634001102300774400⟩,
      ⟨3149, -249489483757418399082069899608064⟩,
      ⟨3193, 610373764009892456820662593388544⟩,
      ⟨3661, -580108605929443479859928804360192⟩,
      ⟨3853, -610532220334920985495849681289216⟩,
      ⟨4007, -317467247194657200737330608996352⟩,
      ⟨4011, -317784159844714258087704784797696⟩,
      ⟨4361, -1382056066898827104981780669661184⟩,
      ⟨4755, 67977763437238801655260709388288⟩,
      ⟨5631, 2178219872004669433459303826587648⟩,
      ⟨5691, 2173149269603756515853317013766144⟩,
      ⟨7291, -577652532891501285394528941899776⟩,
      ⟨7923, 2317265297217203345935973459427328⟩,
      ⟨17339, -1373737109834829349534458554875904⟩,
      ⟨27429, -2173149269603756515853317013766144⟩,
      ⟨27493, -2178219872004669433459303826587648⟩,
      ⟨35901, 1107055114811815589194589618044928⟩,
      ⟨36207, 1105708236049073095455499370889216⟩,
      ⟨70799, 11218549355694801674570636279676928⟩,
      ⟨86107, 3258654324211692205222462677319680⟩,
      ⟨16006959245189, -5609274677847400837285318139838464⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 3210, 5691, 5631, 3193, 258, 1670, 1670, 1670][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 2763, 7923, 7960, 2739, 257, 1776, 1776, 1776][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 4734, 36207, 86107, 35901, 4755, 256, 5564, 5564][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }]
  referenceNumerators := [27, 147, 52, 3, 126, 3149, 4007, 415, 9, 48, 2373, 17339, 7322, 344, 3, 3, 335, 7291, 17444, 2373, 47, 9, 416, 4011, 3144, 124, 3, 53, 155, 27]
  marginalXNumerators := [229, 7706, 27429, 27493, 7704, 238, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 55)
    1 1 55

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13.Parent1
