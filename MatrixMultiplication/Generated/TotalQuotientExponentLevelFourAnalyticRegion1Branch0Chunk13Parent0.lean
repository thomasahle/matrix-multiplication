import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 13, parent 54;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13.Parent0

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 54

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 2981989580711881138345807202746368
  terms := [⟨3, -713053462628379038341895553024⟩,
      ⟨9, -1426106925256758076683791106048⟩,
      ⟨13, -2059932225370872777432142708736⟩,
      ⟨15, -4753689750855860255612637020160⟩,
      ⟨25, -1980704062856608439838598758400⟩,
      ⟨31, -9824292151768777861599449841664⟩,
      ⟨49, -7764359926397905084167307132928⟩,
      ⟨59, -18697846353366383672076372279296⟩,
      ⟨63, -4991374238398653268393268871168⟩,
      ⟨117, -18539390028337854996889284378624⟩,
      ⟨121, -9586607664225984848818817990656⟩,
      ⟨145, -22976167129136657902127745597440⟩,
      ⟨257, 15924860665367131856302334017536⟩,
      ⟨379, -30027473592906183947953157177344⟩,
      ⟨383, -30344386242963241298327332978688⟩,
      ⟨561, -44446999170502293389978156138496⟩,
      ⟨569, -45080824470616408090726507741184⟩,
      ⟨987, -156396392803157802409655757963264⟩,
      ⟨1045, -165586859654812465570506856202240⟩,
      ⟨1123, 363657265940473309554366732042240⟩,
      ⟨1129, 364132634915558895579927995744256⟩,
      ⟨1241, -393288598720808171814352169467904⟩,
      ⟨1297, 83348026965006083148408235753472⟩,
      ⟨1569, 613939031323034352012372071153664⟩,
      ⟨1969, -156000251990586480721688038211584⟩,
      ⟨2083, -165032262517212615207352048549888⟩,
      ⟨2145, -679777634372388016552607093882880⟩,
      ⟨2315, 2371457360376960152849957521457152⟩,
      ⟨2613, 84061080427634462186750131306496⟩,
      ⟨2883, 2105013049841489185522869216477184⟩,
      ⟨3123, 615285910085776845751462318309376⟩,
      ⟨3331, -2111272074680116068192759188553728⟩,
      ⟨3883, -615285910085776845751462318309376⟩,
      ⟨4695, 2351888004235936861464352165724160⟩,
      ⟨4985, -394952390133607722903816592424960⟩,
      ⟨5715, 2111272074680116068192759188553728⟩,
      ⟨7749, -613939031323034352012372071153664⟩,
      ⟨8643, -684769008610786669821000362754048⟩,
      ⟨15517, -1229383397733839726439021477363712⟩,
      ⟨15669, -1241426078436007905753240157814784⟩,
      ⟨19089, 1252438793025490648678742766911488⟩,
      ⟨26569, -2105013049841489185522869216477184⟩,
      ⟨34601, 10965494604624241380296856902303744⟩,
      ⟨37723, 1255132550550975636156923261222912⟩,
      ⟨70399, 2805469234630100194187391281397760⟩,
      ⟨4096972642911, -5482747302312120690148428451151872⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 3138, 5766, 5715, 3123, 256, 1663, 1663, 1663][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 5188, 38178, 70399, 37723, 5226, 256, 5635, 5635][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 2258, 9260, 9390, 2246, 257, 1753, 1753, 1753][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }]
  referenceNumerators := [3, 60, 145, 26, 9, 569, 4964, 2083, 124, 3, 383, 8643, 15517, 1974, 49, 49, 1969, 15669, 8580, 379, 2, 121, 2090, 4985, 561, 9, 25, 145, 63, 3]
  marginalXNumerators := [234, 7749, 26569, 26648, 7766, 236, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 54)
    1 1 54

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13.Parent0
