import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 7, parent 30;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7.Parent0

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 30

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 315803455781857649647866186039296
  terms := [⟨3, -950737950171172051122527404032⟩,
      ⟨5, -6338253001141147007483516026880⟩,
      ⟨7, -6100568513598353994702884175872⟩,
      ⟨13, -1029966112685436388716071354368⟩,
      ⟨17, 475368975085586025561263702016⟩,
      ⟨27, -4278320775770274230051373318144⟩,
      ⟨49, -15528719852795810168334614265856⟩,
      ⟨57, -4516005263313067242832005169152⟩,
      ⟨81, -6417481163655411345077059977216⟩,
      ⟨115, 16241773315424189206676509818880⟩,
      ⟨129, 31849721330734263712604668035072⟩,
      ⟨201, -31849721330734263712604668035072⟩,
      ⟨245, -19410899815994762710418267832320⟩,
      ⟨247, -19569356141023291385605355732992⟩,
      ⟨275, 114563922995626232160264552185856⟩,
      ⟨397, -31453580518162942024636948283392⟩,
      ⟨409, -64808636936668228151518951374848⟩,
      ⟨497, -39376396769589375783991343316992⟩,
      ⟨499, -39534853094617904459178431217664⟩,
      ⟨557, 115514660945797404211387079589888⟩,
      ⟨723, -114563922995626232160264552185856⟩,
      ⟨729, -115514660945797404211387079589888⟩,
      ⟨827, -65521690399296607189860846927872⟩,
      ⟨833, 143086061500761393693940374306816⟩,
      ⟨921, 16321001477938453544270053769216⟩,
      ⟨1023, 135559386061906281622553699024896⟩,
      ⟨1147, 128349623273108226901541199544320⟩,
      ⟨3703, 586763771580641684217786496188416⟩,
      ⟨4607, 128824992248193812927102463246336⟩,
      ⟨9521211903, -293381885790320842108893248094208⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 557, 550, 258, 377, 377, 377, 377, 377][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[737, 272, 256, 921, 4588, 4607, 920, 256, 272][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 1023, 1666, 1023, 256, 648, 648, 648, 648][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 8, z := 0 }, { x := 0, y := 7, z := 1 }, { x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }]
  referenceNumerators := [3, 13, 80, 245, 56, 7, 98, 827, 499, 27, 27, 497, 818, 98, 6, 57, 247, 81, 14, 3]
  marginalXNumerators := [397, 1458, 1446, 402, 0, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 30)
    1 1 30

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7.Parent0
