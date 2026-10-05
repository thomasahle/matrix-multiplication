import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Tactic.FinCases

/-! Root projection for level-four region 1, branch 0, chunk 10, parent 42;
certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The proof is isolated so its exact reconstruction is reclaimed
before the neighboring parent is checked. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10.Parent0

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 42

/-- Canonical exact signed-log form for this one-parent recurrence check. -/
def expectedForm : Form := {
  constantNumerator := 2742403617268745781462930296930304
  terms := [⟨3, -3802951800684688204490109616128⟩,
      ⟨5, -3961408125713216879677197516800⟩,
      ⟨31, -39297168607075111446397799366656⟩,
      ⟨39, -12359593352225236664592856252416⟩,
      ⟨41, -3248354663084837841335301963776⟩,
      ⟨47, 1426106925256758076683791106048⟩,
      ⟨49, -11646539889596857626250960699392⟩,
      ⟨75, -11884224377139650639031592550400⟩,
      ⟨97, -7685131763883640746573763182592⟩,
      ⟨121, -19173215328451969697637635981312⟩,
      ⟨125, 328559189946654208000426762043392⟩,
      ⟨129, 34701935181247779865972250247168⟩,
      ⟨141, -89369367316090172805517575979008⟩,
      ⟨233, -18460161865823590659295740428288⟩,
      ⟨249, 328400733621625679325239674142720⟩,
      ⟨257, 39693309419646433134365519118336⟩,
      ⟨267, 14736438227653166792399174762496⟩,
      ⟨291, -46110790583301844479442579095552⟩,
      ⟨499, 304156915892260792021615225339904⟩,
      ⟨501, -39693309419646433134365519118336⟩,
      ⟨557, -88260173040890472079207960674304⟩,
      ⟨747, -118366874796310920364754661801984⟩,
      ⟨987, 302096983666889919244183082631168⟩,
      ⟨1153, -182700142757893562490712349474816⟩,
      ⟨1327, 613067521535377444298843087699968⟩,
      ⟨1497, -118604559283853713377535293652992⟩,
      ⟨1701, 673677065858789662557904209707008⟩,
      ⟨2135, 14815666390167431129992718712832⟩,
      ⟨2317, -183571652545550470204241332928512⟩,
      ⟨3869, -613067521535377444298843087699968⟩,
      ⟨4145, -328400733621625679325239674142720⟩,
      ⟨4147, -328559189946654208000426762043392⟩,
      ⟨5415, -429020500014741388069040491069440⟩,
      ⟨12213, 819536113047550308067618622275584⟩,
      ⟨17027, 2698035846260757752410545684742144⟩,
      ⟨18353, 249489483757418399082069899608064⟩,
      ⟨18363, 248855658457304284381321548005376⟩,
      ⟨350905531907, -1349017923130378876205272842371072⟩]
}

/-- Small literal projection containing exactly the fields used by the logical-`X` form. -/
def emptyCompatibilityRows :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  { pooled := [], first := [], groups := [] }

def expectedWeightX (value : Fin 9) : ℕ :=
  #[256, 1000, 1327, 996, 257, 613, 613, 613, 613][value.val]?.getD 0

def expectedWeightY (value : Fin 9) : ℕ :=
  #[256, 376, 2136, 18363, 48852, 18353, 2135, 376, 256][value.val]?.getD 0

def expectedWeightZ (value : Fin 9) : ℕ :=
  #[256, 998, 1701, 987, 258, 644, 644, 644, 644][value.val]?.getD 0

def expectedRootRows : LocalRows 9 := {
  support := [{ x := 0, y := 8, z := 0 }, { x := 0, y := 7, z := 1 }, { x := 0, y := 6, z := 2 }, { x := 0, y := 5, z := 3 }, { x := 0, y := 4, z := 4 }, { x := 1, y := 7, z := 0 }, { x := 1, y := 6, z := 1 }, { x := 1, y := 5, z := 2 }, { x := 1, y := 4, z := 3 }, { x := 1, y := 3, z := 4 }, { x := 2, y := 6, z := 0 }, { x := 2, y := 5, z := 1 }, { x := 2, y := 4, z := 2 }, { x := 2, y := 3, z := 3 }, { x := 2, y := 2, z := 4 }, { x := 3, y := 5, z := 0 }, { x := 3, y := 4, z := 1 }, { x := 3, y := 3, z := 2 }, { x := 3, y := 2, z := 3 }, { x := 3, y := 1, z := 4 }, { x := 4, y := 4, z := 0 }, { x := 4, y := 3, z := 1 }, { x := 4, y := 2, z := 2 }, { x := 4, y := 1, z := 3 }, { x := 4, y := 0, z := 4 }]
  referenceNumerators := [1, 5, 49, 291, 150, 4, 98, 1497, 2306, 242, 40, 1128, 5415, 1114, 41, 233, 2317, 1494, 97, 4, 156, 291, 48, 5, 1]
  marginalXNumerators := [496, 4147, 7738, 4145, 501, 0, 0, 0, 0]
  weightX := expectedWeightX
  weightY := expectedWeightY
  weightZ := expectedWeightZ
  logicalY := emptyCompatibilityRows
  logicalZ := emptyCompatibilityRows
}

def actualRootRows : LocalRows 9 :=
  localRowsFrom Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) (Weights.Region1.dualWeights 42)
    1 1 42

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10.Parent0
