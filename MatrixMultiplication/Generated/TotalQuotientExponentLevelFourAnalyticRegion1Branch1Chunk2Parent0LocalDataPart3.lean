import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk2Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 1,
parent 9; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot11

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨11, 1, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 411, numerator := 149906801632214017663565824 }, some { target := 412, numerator := 169249614746048084458864640 }, some { target := 413, numerator := 145071098353755500964741120 }, some { target := 414, numerator := 1910102794991114096035758080 }, some { target := 415, numerator := 169249614746048084458864640 }, some { target := 416, numerator := 145071098353755500964741120 }, some { target := 417, numerator := 169249614746048084458864640 }, some { target := 418, numerator := 169249614746048084458864640 }, some { target := 419, numerator := 7016605457043307729994645504 }, some { target := 420, numerator := 174085318024506601157689344 }, some { target := 421, numerator := 1910102794991114096035758080 }, some { target := 422, numerator := 7016605457043307729994645504 }, some { target := 423, numerator := 149906801632214017663565824 }, some { target := 424, numerator := 169249614746048084458864640 }, some { target := 425, numerator := 174085318024506601157689344 }, some { target := 426, numerator := 169249614746048084458864640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 149906801632214017663565824 }, some { target := 628, numerator := 169249614746048084458864640 }, some { target := 629, numerator := 145071098353755500964741120 }, some { target := 630, numerator := 1910102794991114096035758080 }, some { target := 631, numerator := 169249614746048084458864640 }, some { target := 632, numerator := 145071098353755500964741120 }, some { target := 633, numerator := 169249614746048084458864640 }, some { target := 634, numerator := 169249614746048084458864640 }, some { target := 635, numerator := 7016605457043307729994645504 }, some { target := 636, numerator := 174085318024506601157689344 }, some { target := 637, numerator := 1910102794991114096035758080 }, some { target := 638, numerator := 7016605457043307729994645504 }, some { target := 639, numerator := 149906801632214017663565824 }, some { target := 640, numerator := 169249614746048084458864640 }, some { target := 641, numerator := 174085318024506601157689344 }, some { target := 642, numerator := 169249614746048084458864640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 723, numerator := 149906801632214017663565824 }, some { target := 724, numerator := 169249614746048084458864640 }, some { target := 725, numerator := 145071098353755500964741120 }, some { target := 726, numerator := 1910102794991114096035758080 }, some { target := 727, numerator := 169249614746048084458864640 }, some { target := 728, numerator := 145071098353755500964741120 }, some { target := 729, numerator := 169249614746048084458864640 }, some { target := 730, numerator := 169249614746048084458864640 }, some { target := 731, numerator := 7016605457043307729994645504 }, some { target := 732, numerator := 174085318024506601157689344 }, some { target := 733, numerator := 1910102794991114096035758080 }, some { target := 734, numerator := 7016605457043307729994645504 }, some { target := 735, numerator := 149906801632214017663565824 }, some { target := 736, numerator := 169249614746048084458864640 }, some { target := 737, numerator := 174085318024506601157689344 }, some { target := 738, numerator := 169249614746048084458864640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 758, numerator := 149906801632214017663565824 }, some { target := 759, numerator := 169249614746048084458864640 }, some { target := 760, numerator := 145071098353755500964741120 }, some { target := 761, numerator := 1910102794991114096035758080 }, some { target := 762, numerator := 169249614746048084458864640 }, some { target := 763, numerator := 145071098353755500964741120 }, some { target := 764, numerator := 169249614746048084458864640 }, some { target := 765, numerator := 169249614746048084458864640 }, some { target := 766, numerator := 7016605457043307729994645504 }, some { target := 767, numerator := 174085318024506601157689344 }, some { target := 768, numerator := 1910102794991114096035758080 }, some { target := 769, numerator := 7016605457043307729994645504 }, some { target := 770, numerator := 149906801632214017663565824 }, some { target := 771, numerator := 169249614746048084458864640 }, some { target := 772, numerator := 174085318024506601157689344 }, some { target := 773, numerator := 169249614746048084458864640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq]
  rfl

end Slot11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2.Parent0
