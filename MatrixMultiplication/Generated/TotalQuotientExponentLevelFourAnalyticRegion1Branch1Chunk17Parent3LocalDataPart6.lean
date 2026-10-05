import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk17Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 1,
parent 73; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 31, #[1924145348608, 38482906972160, 1992864825344, 35802847379456, 53601191854080, 1924145348608, 53669911330816, 53669911330816, 38414187495424, 1992864825344, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3434312892416, 0, 137303192240128, 0, 0, 137303158685696, 0, 0, 0, 0, 0, 0, 3434312892416, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

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
  [some { target := 35, numerator := 204851632505808726700064768 }, some { target := 37, numerator := 8189930259634042261202796544 }, some { target := 40, numerator := 8189928258162310263716446208 }, some { target := 47, numerator := 204851632505808726700064768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 70, numerator := 4097032650116174534001295360 }, some { target := 72, numerator := 163798605192680845224055930880 }, some { target := 75, numerator := 163798565163246205274328924160 }, some { target := 82, numerator := 4097032650116174534001295360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 96, numerator := 212167762238159038367924224 }, some { target := 98, numerator := 8482427768906686627674324992 }, some { target := 101, numerator := 8482425695953821344563462144 }, some { target := 108, numerator := 212167762238159038367924224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 145, numerator := 3811703590554512378954776576 }, some { target := 147, numerator := 152391202331047714931666321408 }, some { target := 150, numerator := 152391165089377273121295302656 }, some { target := 157, numerator := 3811703590554512378954776576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 5706581191233243100930375680 }, some { target := 173, numerator := 228148057232662605847792189440 }, some { target := 176, numerator := 228148001477378643060672430080 }, some { target := 183, numerator := 5706581191233243100930375680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 204851632505808726700064768 }, some { target := 218, numerator := 8189930259634042261202796544 }, some { target := 221, numerator := 8189928258162310263716446208 }, some { target := 228, numerator := 204851632505808726700064768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 285, numerator := 5713897320965593412598235136 }, some { target := 287, numerator := 228440554741935250214263717888 }, some { target := 290, numerator := 228440498915170154141519446016 }, some { target := 297, numerator := 5713897320965593412598235136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 311, numerator := 5713897320965593412598235136 }, some { target := 313, numerator := 228440554741935250214263717888 }, some { target := 316, numerator := 228440498915170154141519446016 }, some { target := 323, numerator := 5713897320965593412598235136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 356, numerator := 4089716520383824222333435904 }, some { target := 358, numerator := 163506107683408200857584402432 }, some { target := 361, numerator := 163506067725454694193481908224 }, some { target := 368, numerator := 4089716520383824222333435904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 427, numerator := 212167762238159038367924224 }, some { target := 429, numerator := 8482427768906686627674324992 }, some { target := 432, numerator := 8482425695953821344563462144 }, some { target := 439, numerator := 212167762238159038367924224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq]
  rfl

end Slot25

namespace Slot26

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨26, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot26

namespace Slot27

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨27, 1, #[67070209294336, 73667279060992, 67070209294336, 73667279060992, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 16, numerator := 27654178123684642371403776 }, some { target := 17, numerator := 400985582793427314385354752 }, some { target := 18, numerator := 709790571841239154199363584 }, some { target := 19, numerator := 23045148436403868642836480 }, some { target := 20, numerator := 442466849978954277942460416 }, some { target := 21, numerator := 23045148436403868642836480 }, some { target := 22, numerator := 705181542153958380470796288 }, some { target := 23, numerator := 737444749964923796570767360 }, some { target := 24, numerator := 442466849978954277942460416 }, some { target := 25, numerator := 11296731763525176408718442496 }, some { target := 26, numerator := 723617660903081475385065472 }, some { target := 27, numerator := 400985582793427314385354752 }, some { target := 28, numerator := 705181542153958380470796288 }, some { target := 29, numerator := 23045148436403868642836480 }, some { target := 30, numerator := 723617660903081475385065472 }, some { target := 31, numerator := 23045148436403868642836480 }, some { target := 32, numerator := 705181542153958380470796288 }, some { target := 33, numerator := 737444749964923796570767360 }, some { target := 34, numerator := 27654178123684642371403776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 30374261217817558014492672 }, some { target := 52, numerator := 440426787658354591210143744 }, some { target := 53, numerator := 779606037923983989038645248 }, some { target := 54, numerator := 25311884348181298345410560 }, some { target := 55, numerator := 485988179485080928231882752 }, some { target := 56, numerator := 25311884348181298345410560 }, some { target := 57, numerator := 774543661054347729369563136 }, some { target := 58, numerator := 809980299141801547053137920 }, some { target := 59, numerator := 485988179485080928231882752 }, some { target := 60, numerator := 12407885707478472448920256512 }, some { target := 61, numerator := 794793168532892768045891584 }, some { target := 62, numerator := 440426787658354591210143744 }, some { target := 63, numerator := 774543661054347729369563136 }, some { target := 64, numerator := 25311884348181298345410560 }, some { target := 65, numerator := 794793168532892768045891584 }, some { target := 66, numerator := 25311884348181298345410560 }, some { target := 67, numerator := 774543661054347729369563136 }, some { target := 68, numerator := 809980299141801547053137920 }, some { target := 69, numerator := 30374261217817558014492672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 27654178123684642371403776 }, some { target := 127, numerator := 400985582793427314385354752 }, some { target := 128, numerator := 709790571841239154199363584 }, some { target := 129, numerator := 23045148436403868642836480 }, some { target := 130, numerator := 442466849978954277942460416 }, some { target := 131, numerator := 23045148436403868642836480 }, some { target := 132, numerator := 705181542153958380470796288 }, some { target := 133, numerator := 737444749964923796570767360 }, some { target := 134, numerator := 442466849978954277942460416 }, some { target := 135, numerator := 11296731763525176408718442496 }, some { target := 136, numerator := 723617660903081475385065472 }, some { target := 137, numerator := 400985582793427314385354752 }, some { target := 138, numerator := 705181542153958380470796288 }, some { target := 139, numerator := 23045148436403868642836480 }, some { target := 140, numerator := 723617660903081475385065472 }, some { target := 141, numerator := 23045148436403868642836480 }, some { target := 142, numerator := 705181542153958380470796288 }, some { target := 143, numerator := 737444749964923796570767360 }, some { target := 144, numerator := 27654178123684642371403776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 266, numerator := 30374261217817558014492672 }, some { target := 267, numerator := 440426787658354591210143744 }, some { target := 268, numerator := 779606037923983989038645248 }, some { target := 269, numerator := 25311884348181298345410560 }, some { target := 270, numerator := 485988179485080928231882752 }, some { target := 271, numerator := 25311884348181298345410560 }, some { target := 272, numerator := 774543661054347729369563136 }, some { target := 273, numerator := 809980299141801547053137920 }, some { target := 274, numerator := 485988179485080928231882752 }, some { target := 275, numerator := 12407885707478472448920256512 }, some { target := 276, numerator := 794793168532892768045891584 }, some { target := 277, numerator := 440426787658354591210143744 }, some { target := 278, numerator := 774543661054347729369563136 }, some { target := 279, numerator := 25311884348181298345410560 }, some { target := 280, numerator := 794793168532892768045891584 }, some { target := 281, numerator := 25311884348181298345410560 }, some { target := 282, numerator := 774543661054347729369563136 }, some { target := 283, numerator := 809980299141801547053137920 }, some { target := 284, numerator := 30374261217817558014492672 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17.Parent3
