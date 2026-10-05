import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk17Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 1,
parent 72; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot26

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨26, 1, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        0 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 0, numerator := 116056878683004400771792896 }, some { target := 1, numerator := 1682824740903563811190996992 }, some { target := 2, numerator := 2978793219530446286476017664 }, some { target := 3, numerator := 96714065569170333976494080 }, some { target := 4, numerator := 1856910058928070412348686336 }, some { target := 5, numerator := 96714065569170333976494080 }, some { target := 6, numerator := 2959450406416612219680718848 }, some { target := 7, numerator := 3094850098213450687247810560 }, some { target := 8, numerator := 1856910058928070412348686336 }, some { target := 9, numerator := 47409234942007297715277398016 }, some { target := 10, numerator := 3036821658871948486861914112 }, some { target := 11, numerator := 1682824740903563811190996992 }, some { target := 12, numerator := 2959450406416612219680718848 }, some { target := 13, numerator := 96714065569170333976494080 }, some { target := 14, numerator := 3036821658871948486861914112 }, some { target := 15, numerator := 96714065569170333976494080 }, some { target := 16, numerator := 2959450406416612219680718848 }, some { target := 17, numerator := 3094850098213450687247810560 }, some { target := 18, numerator := 116056878683004400771792896 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq]
  rfl

end Slot26

namespace Slot27

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨27, 1, #[67070209294336, 73667279060992, 67070209294336, 73667279060992, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

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
  [some { target := 19, numerator := 142879920305703985585586176 }, some { target := 20, numerator := 161316039054827080499855360 }, some { target := 21, numerator := 138270890618423211857018880 }, some { target := 22, numerator := 1820566726475905622784081920 }, some { target := 23, numerator := 161316039054827080499855360 }, some { target := 24, numerator := 138270890618423211857018880 }, some { target := 25, numerator := 161316039054827080499855360 }, some { target := 26, numerator := 161316039054827080499855360 }, some { target := 27, numerator := 6687702076244402680151146496 }, some { target := 28, numerator := 165925068742107854228422656 }, some { target := 29, numerator := 1820566726475905622784081920 }, some { target := 30, numerator := 6687702076244402680151146496 }, some { target := 31, numerator := 142879920305703985585586176 }, some { target := 32, numerator := 161316039054827080499855360 }, some { target := 33, numerator := 165925068742107854228422656 }, some { target := 34, numerator := 161316039054827080499855360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 45, numerator := 156933682958724049741545472 }, some { target := 46, numerator := 177183190437269088417873920 }, some { target := 47, numerator := 151871306089087790072463360 }, some { target := 48, numerator := 1999638863506322569287434240 }, some { target := 49, numerator := 177183190437269088417873920 }, some { target := 50, numerator := 151871306089087790072463360 }, some { target := 51, numerator := 177183190437269088417873920 }, some { target := 52, numerator := 177183190437269088417873920 }, some { target := 53, numerator := 7345508837842212779838144512 }, some { target := 54, numerator := 182245567306905348086956032 }, some { target := 55, numerator := 1999638863506322569287434240 }, some { target := 56, numerator := 7345508837842212779838144512 }, some { target := 57, numerator := 156933682958724049741545472 }, some { target := 58, numerator := 177183190437269088417873920 }, some { target := 59, numerator := 182245567306905348086956032 }, some { target := 60, numerator := 177183190437269088417873920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 142879920305703985585586176 }, some { target := 91, numerator := 161316039054827080499855360 }, some { target := 92, numerator := 138270890618423211857018880 }, some { target := 93, numerator := 1820566726475905622784081920 }, some { target := 94, numerator := 161316039054827080499855360 }, some { target := 95, numerator := 138270890618423211857018880 }, some { target := 96, numerator := 161316039054827080499855360 }, some { target := 97, numerator := 161316039054827080499855360 }, some { target := 98, numerator := 6687702076244402680151146496 }, some { target := 99, numerator := 165925068742107854228422656 }, some { target := 100, numerator := 1820566726475905622784081920 }, some { target := 101, numerator := 6687702076244402680151146496 }, some { target := 102, numerator := 142879920305703985585586176 }, some { target := 103, numerator := 161316039054827080499855360 }, some { target := 104, numerator := 165925068742107854228422656 }, some { target := 105, numerator := 161316039054827080499855360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 161, numerator := 156933682958724049741545472 }, some { target := 162, numerator := 177183190437269088417873920 }, some { target := 163, numerator := 151871306089087790072463360 }, some { target := 164, numerator := 1999638863506322569287434240 }, some { target := 165, numerator := 177183190437269088417873920 }, some { target := 166, numerator := 151871306089087790072463360 }, some { target := 167, numerator := 177183190437269088417873920 }, some { target := 168, numerator := 177183190437269088417873920 }, some { target := 169, numerator := 7345508837842212779838144512 }, some { target := 170, numerator := 182245567306905348086956032 }, some { target := 171, numerator := 1999638863506322569287434240 }, some { target := 172, numerator := 7345508837842212779838144512 }, some { target := 173, numerator := 156933682958724049741545472 }, some { target := 174, numerator := 177183190437269088417873920 }, some { target := 175, numerator := 182245567306905348086956032 }, some { target := 176, numerator := 177183190437269088417873920 }]

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

end Slot27

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17.Parent2
