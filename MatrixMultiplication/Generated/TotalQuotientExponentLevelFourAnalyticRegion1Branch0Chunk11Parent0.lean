import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 11, parent 46;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk11.Parent0

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 46

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 6691135236979680367125160781676544
  terms := [⟨5, -1584563250285286751870879006720⟩,
      ⟨7, -17747108403195211620953844875264⟩,
      ⟨19, -96341445617345434513749443608576⟩,
      ⟨21, -16637914127995510894644229570560⟩,
      ⟨41, -3248354663084837841335301963776⟩,
      ⟨43, -6813621976226733033044779728896⟩,
      ⟨47, 1584563250285286751870879006720⟩,
      ⟨65, 319368723094999544839575663804416⟩,
      ⟨71, -22500798154051071876566481895424⟩,
      ⟨83, -13151874977367880040528295755776⟩,
      ⟨117, 13389559464910673053308927606784⟩,
      ⟨125, -39614081257132168796771975168000⟩,
      ⟨129, -81763463714720796396537356746752⟩,
      ⟨139, -22025429178965485851005218193408⟩,
      ⟨173, -13706472114967730403683103408128⟩,
      ⟨231, -18301705540795061984108652527616⟩,
      ⟨259, 318417985144828372788453136400384⟩,
      ⟨495, 329113787084254058363581569695744⟩,
      ⟨499, -39534853094617904459178431217664⟩,
      ⟨655, -207577785787372564495085149880320⟩,
      ⟨935, 13310331302396408715715383656448⟩,
      ⟨989, 328717646271682736675613849944064⟩,
      ⟨1039, -82318060852320646759692164399104⟩,
      ⟨1215, -96262217454831170176155899658240⟩,
      ⟨1333, 602530175920980287398901742305280⟩,
      ⟨1557, 873807404369821379319196228255744⟩,
      ⟨1595, 631289998913658241945358196277248⟩,
      ⟨1937, 218273587726798250070213583175680⟩,
      ⟨2077, -329113787084254058363581569695744⟩,
      ⟨2619, -207498557624858300157491605929984⟩,
      ⟨4149, -328717646271682736675613849944064⟩,
      ⟨5451, -431872713865254904222408073281536⟩,
      ⟨7605, -602530175920980287398901742305280⟩,
      ⟨15541, 218986641189426629108555478728704⟩,
      ⟨16907, 2679021087257334311388095136661504⟩,
      ⟨329922106235, -1339510543628667155694047568330752⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 990, 1333, 989, 256, 612, 612, 612, 612][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 1036, 1595, 1040, 256, 646, 646, 646, 646][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 376, 1870, 15541, 49824, 15496, 1872, 376, 256][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 4, z := 4 }, { x := 0, y := 3, z := 5 }, { x := 0, y := 2, z := 6 }, { x := 0, y := 1, z := 7 }, { x := 0, y := 0, z := 8 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 1, y := 2, z := 5 }, { x := 1, y := 1, z := 6 }, { x := 1, y := 0, z := 7 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 2, y := 1, z := 5 }, { x := 2, y := 0, z := 6 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 3, y := 0, z := 5 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }]
  referenceNumerators := [166, 284, 43, 5, 1, 231, 2619, 1215, 84, 5, 41, 1039, 5451, 1032, 42, 5, 84, 1216, 2620, 224, 1, 5, 43, 278, 173]
  marginalXNumerators := [499, 4154, 7605, 4149, 500, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 46)
    1 1 46

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk11.Parent0
