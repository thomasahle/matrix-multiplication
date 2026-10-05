import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 19, parent 80;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19.Parent2

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 80

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 4145772059883909993257374289231872
  terms := [⟨5, -792281625142643375935439503360⟩,
      ⟨9, -1426106925256758076683791106048⟩,
      ⟨23, -3644495475656159529303021715456⟩,
      ⟨25, -7922816251426433759354395033600⟩,
      ⟨27, -8556641551540548460102746636288⟩,
      ⟨31, -9824292151768777861599449841664⟩,
      ⟨49, -3882179963198952542083653566464⟩,
      ⟨51, -16162545152909924869082965868544⟩,
      ⟨103, -16321001477938453544270053769216⟩,
      ⟨107, -8477413389026284122509202685952⟩,
      ⟨123, -9745063989254513524005905891328⟩,
      ⟨129, -20440865928680199099134339186688⟩,
      ⟨189, 1426106925256758076683791106048⟩,
      ⟨217, 676766964196845971724052423770112⟩,
      ⟨257, 34543478856219251190785162346496⟩,
      ⟨259, -20520094091194463436727883137024⟩,
      ⟨261, -20678550416222992111914971037696⟩,
      ⟨495, 289182793177064832216435418726400⟩,
      ⟨507, 16162545152909924869082965868544⟩,
      ⟨515, 306929901580260043837389263601664⟩,
      ⟨691, -218986641189426629108555478728704⟩,
      ⟨789, 638975130677541882691931959459840⟩,
      ⟨881, -279200044700267525679648880984064⟩,
      ⟨947, -150058139802016655402172241936384⟩,
      ⟨987, 288707424201979246190874155024384⟩,
      ⟨1031, 307722183205402687213324703105024⟩,
      ⟨1613, -127795026135508376538386391891968⟩,
      ⟨1623, -128587307760651019914321831395328⟩,
      ⟨1755, -278090850425067824953339265679360⟩,
      ⟨1891, -149820455314473862389391610085376⟩,
      ⟨2029, 16321001477938453544270053769216⟩,
      ⟨2603, -412461814049260141511989805449216⟩,
      ⟨4619, -731909765306773950689159013203968⟩,
      ⟨8351, 2646537540626485932974742117023744⟩,
      ⟨18617, 278090850425067824953339265679360⟩,
      ⟨18695, 279200044700267525679648880984064⟩,
      ⟨38591, 731909765306773950689159013203968⟩,
      ⟨341663379085, -1323268770313242966487371058511872⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 378, 2029, 18695, 38591, 18617, 2028, 378, 256][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 1030, 1578, 1031, 256, 643, 643, 643, 643][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 990, 1736, 987, 257, 645, 645, 645, 645][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 4, z := 4 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }, { x := 5, y := 3, z := 0 }, { x := 5, y := 2, z := 1 }, { x := 5, y := 1, z := 2 }, { x := 5, y := 0, z := 3 }, { x := 6, y := 2, z := 0 }, { x := 6, y := 1, z := 1 }, { x := 6, y := 0, z := 2 }, { x := 7, y := 1, z := 0 }, { x := 7, y := 0, z := 1 }, { x := 8, y := 0, z := 0 }]
  referenceNumerators := [1, 5, 4, 50, 107, 49, 261, 1623, 1382, 258, 123, 1894, 5206, 1891, 124, 256, 1382, 1613, 259, 46, 108, 50, 4, 5, 1]
  marginalXNumerators := [1, 9, 206, 3524, 9238, 3510, 204, 9, 1]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 80)
    1 1 80

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19.Parent2
