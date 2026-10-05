import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 18, parent 75;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18.Parent1

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 75

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 206389363349658599431181990625280
  terms := [⟨3, -950737950171172051122527404032⟩,
      ⟨7, -1109194275199700726309615304704⟩,
      ⟨37, -187612288833777951421512074395648⟩,
      ⟨59, -9348923176683191836038186139648⟩,
      ⟨123, -9745063989254513524005905891328⟩,
      ⟨153, -24243817729364887303624448802816⟩,
      ⟨159, -25194555679536059354746976206848⟩,
      ⟨261, 191415240634462639626002184011776⟩,
      ⟨271, -42941664082731270975700821082112⟩,
      ⟨325, -51498305634271819435803567718400⟩,
      ⟨333, -52765956234500048837300270923776⟩,
      ⟨383, 395903128083778894954939119828992⟩,
      ⟨389, -123279020872195309295554386722816⟩,
      ⟨473, 1267650600228229401496703205376⟩,
      ⟨521, -41277872669931719886236398125056⟩,
      ⟨1193, -189038395759034709498195865501696⟩,
      ⟨1543, -122249054759509872906838315368448⟩,
      ⟨1951, 1109194275199700726309615304704⟩,
      ⟨2121, -336085865385509320071813437325312⟩,
      ⟨4235, -335531268247909469708658629672960⟩,
      ⟨9809, 1554298092204837774910145217691648⟩,
      ⟨12955, 34147338043647929502817442594816⟩,
      ⟨13217, 52765956234500048837300270923776⟩,
      ⟨26253, 51498305634271819435803567718400⟩,
      ⟨26325, 35494216806390423241907689750528⟩,
      ⟨60463, 351139216263219544214586787889152⟩,
      ⟨61607, 355259080713961289769451073306624⟩,
      ⟨101675, 335531268247909469708658629672960⟩,
      ⟨102643, 336085865385509320071813437325312⟩,
      ⟨19623664279671, -777149046102418887455072608845824⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 1892, 26253, 102643, 101675, 26434, 1892, 256, 6009][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[261, 383, 256, 295, 295, 295, 295, 295, 295][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 1951, 25910, 123214, 120926, 26325, 1951, 256, 6317][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 2, z := 6 }, { x := 0, y := 1, z := 7 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }]
  referenceNumerators := [0, 0, 7, 1, 0, 521, 123, 6, 1556, 2368, 318, 306, 2386, 1543, 6, 118, 542, 0, 1, 7, 0, 0]
  marginalXNumerators := [0, 8, 650, 4242, 4235, 666, 8, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 75)
    1 1 75

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18.Parent1
