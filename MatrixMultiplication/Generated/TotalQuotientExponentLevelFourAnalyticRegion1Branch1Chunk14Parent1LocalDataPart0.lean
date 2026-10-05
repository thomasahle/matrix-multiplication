import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk14Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 59; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 1, #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0]⟩

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
  [some { target := 411, numerator := 174765338798039830068461568 }, some { target := 412, numerator := 199038302519989806466859008 }, some { target := 413, numerator := 155346967820479848949743616 }, some { target := 414, numerator := 2082620287343307974982500352 }, some { target := 415, numerator := 184474524286819820627820544 }, some { target := 416, numerator := 155346967820479848949743616 }, some { target := 417, numerator := 184474524286819820627820544 }, some { target := 418, numerator := 179619931542429825348141056 }, some { target := 419, numerator := 6786720656657213400991924224 }, some { target := 420, numerator := 179619931542429825348141056 }, some { target := 421, numerator := 2082620287343307974982500352 }, some { target := 422, numerator := 6786720656657213400991924224 }, some { target := 423, numerator := 174765338798039830068461568 }, some { target := 424, numerator := 179619931542429825348141056 }, some { target := 425, numerator := 179619931542429825348141056 }, some { target := 426, numerator := 199038302519989806466859008 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 174255323217889908385382400 }, some { target := 628, numerator := 198457451442596840105574400 }, some { target := 629, numerator := 154893620638124363009228800 }, some { target := 630, numerator := 2076542601679854741592473600 }, some { target := 631, numerator := 183936174507772681073459200 }, some { target := 632, numerator := 154893620638124363009228800 }, some { target := 633, numerator := 183936174507772681073459200 }, some { target := 634, numerator := 179095748862831294729420800 }, some { target := 635, numerator := 6766915051628058108965683200 }, some { target := 636, numerator := 179095748862831294729420800 }, some { target := 637, numerator := 2076542601679854741592473600 }, some { target := 638, numerator := 6766915051628058108965683200 }, some { target := 639, numerator := 174255323217889908385382400 }, some { target := 640, numerator := 179095748862831294729420800 }, some { target := 641, numerator := 179095748862831294729420800 }, some { target := 642, numerator := 198457451442596840105574400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 723, numerator := 173065286864206757791531008 }, some { target := 724, numerator := 197102132262013251929243648 }, some { target := 725, numerator := 153835810545961562481360896 }, some { target := 726, numerator := 2062361335131797197015744512 }, some { target := 727, numerator := 182680025023329355446616064 }, some { target := 728, numerator := 153835810545961562481360896 }, some { target := 729, numerator := 182680025023329355446616064 }, some { target := 730, numerator := 177872655943768056619073536 }, some { target := 731, numerator := 6720701973226695760904454144 }, some { target := 732, numerator := 177872655943768056619073536 }, some { target := 733, numerator := 2062361335131797197015744512 }, some { target := 734, numerator := 6720701973226695760904454144 }, some { target := 735, numerator := 173065286864206757791531008 }, some { target := 736, numerator := 177872655943768056619073536 }, some { target := 737, numerator := 177872655943768056619073536 }, some { target := 738, numerator := 197102132262013251929243648 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 758, numerator := 174255323217889908385382400 }, some { target := 759, numerator := 198457451442596840105574400 }, some { target := 760, numerator := 154893620638124363009228800 }, some { target := 761, numerator := 2076542601679854741592473600 }, some { target := 762, numerator := 183936174507772681073459200 }, some { target := 763, numerator := 154893620638124363009228800 }, some { target := 764, numerator := 183936174507772681073459200 }, some { target := 765, numerator := 179095748862831294729420800 }, some { target := 766, numerator := 6766915051628058108965683200 }, some { target := 767, numerator := 179095748862831294729420800 }, some { target := 768, numerator := 2076542601679854741592473600 }, some { target := 769, numerator := 6766915051628058108965683200 }, some { target := 770, numerator := 174255323217889908385382400 }, some { target := 771, numerator := 179095748862831294729420800 }, some { target := 772, numerator := 179095748862831294729420800 }, some { target := 773, numerator := 198457451442596840105574400 }]

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

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 1, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        8 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 774, numerator := 14016437068339462480190242816 }, some { target := 777, numerator := 51195293099951895502808678400 }, some { target := 779, numerator := 14016432345972979610545029120 }]

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

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 9, #[5963008442368, 0, 269517133447168, 0, 0, 0, 0, 5994834821120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2, 7]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

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
  [some { target := 142, numerator := 22127840276321486128545792 }, some { target := 143, numerator := 331917604144822291928186880 }, some { target := 144, numerator := 582699793943132468051705856 }, some { target := 145, numerator := 22127840276321486128545792 }, some { target := 146, numerator := 368797337938691435475763200 }, some { target := 147, numerator := 22127840276321486128545792 }, some { target := 148, numerator := 582699793943132468051705856 }, some { target := 149, numerator := 579011820563745553696948224 }, some { target := 150, numerator := 368797337938691435475763200 }, some { target := 151, numerator := 8935959498254493481577742336 }, some { target := 152, numerator := 571635873804971724987432960 }, some { target := 153, numerator := 331917604144822291928186880 }, some { target := 154, numerator := 582699793943132468051705856 }, some { target := 155, numerator := 22127840276321486128545792 }, some { target := 156, numerator := 571635873804971724987432960 }, some { target := 157, numerator := 22127840276321486128545792 }, some { target := 158, numerator := 582699793943132468051705856 }, some { target := 159, numerator := 582699793943132468051705856 }, some { target := 160, numerator := 22127840276321486128545792 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 1000138124621307718498516992 }, some { target := 358, numerator := 15002071869319615777477754880 }, some { target := 359, numerator := 26336970615027769920460947456 }, some { target := 360, numerator := 1000138124621307718498516992 }, some { target := 361, numerator := 16668968743688461974975283200 }, some { target := 362, numerator := 1000138124621307718498516992 }, some { target := 363, numerator := 26336970615027769920460947456 }, some { target := 364, numerator := 26170280927590885300711194624 }, some { target := 365, numerator := 16668968743688461974975283200 }, some { target := 366, numerator := 403889112659571433653651111936 }, some { target := 367, numerator := 25836901552717116061211688960 }, some { target := 368, numerator := 15002071869319615777477754880 }, some { target := 369, numerator := 26336970615027769920460947456 }, some { target := 370, numerator := 1000138124621307718498516992 }, some { target := 371, numerator := 25836901552717116061211688960 }, some { target := 372, numerator := 1000138124621307718498516992 }, some { target := 373, numerator := 26336970615027769920460947456 }, some { target := 374, numerator := 26336970615027769920460947456 }, some { target := 375, numerator := 1000138124621307718498516992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 22245943249410402319073280 }, some { target := 670, numerator := 333689148741156034786099200 }, some { target := 671, numerator := 585809838901140594402263040 }, some { target := 672, numerator := 22245943249410402319073280 }, some { target := 673, numerator := 370765720823506705317888000 }, some { target := 674, numerator := 22245943249410402319073280 }, some { target := 675, numerator := 585809838901140594402263040 }, some { target := 676, numerator := 582102181692905527349084160 }, some { target := 677, numerator := 370765720823506705317888000 }, some { target := 678, numerator := 8983653415553567469852426240 }, some { target := 679, numerator := 574686867276435393242726400 }, some { target := 680, numerator := 333689148741156034786099200 }, some { target := 681, numerator := 585809838901140594402263040 }, some { target := 682, numerator := 22245943249410402319073280 }, some { target := 683, numerator := 574686867276435393242726400 }, some { target := 684, numerator := 22245943249410402319073280 }, some { target := 685, numerator := 585809838901140594402263040 }, some { target := 686, numerator := 585809838901140594402263040 }, some { target := 687, numerator := 22245943249410402319073280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected ++ Left7.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq, Left7.routed_eq]
  rfl

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 5, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 411, numerator := 1237773575866859119905341440 }, some { target := 413, numerator := 48279833898506455463116144640 }, some { target := 416, numerator := 48279816189632144701946593280 }, some { target := 423, numerator := 1237779478824962706961858560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 1237773575866859119905341440 }, some { target := 629, numerator := 48279833898506455463116144640 }, some { target := 632, numerator := 48279816189632144701946593280 }, some { target := 639, numerator := 1237779478824962706961858560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 723, numerator := 1237773575866859119905341440 }, some { target := 725, numerator := 48279833898506455463116144640 }, some { target := 728, numerator := 48279816189632144701946593280 }, some { target := 735, numerator := 1237779478824962706961858560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 758, numerator := 1237773575866859119905341440 }, some { target := 760, numerator := 48279833898506455463116144640 }, some { target := 763, numerator := 48279816189632144701946593280 }, some { target := 770, numerator := 1237779478824962706961858560 }]

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

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 50, #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0], #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 6, 14]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 131590771187010771930316800 }, some { target := 56, numerator := 98693078390258078947737600 }, some { target := 57, numerator := 104176027189716861111500800 }, some { target := 58, numerator := 134332245586740163012198400 }, some { target := 59, numerator := 1798407206222480549714329600 }, some { target := 60, numerator := 3144471136489611570918195200 }, some { target := 61, numerator := 95951603990528687865856000 }, some { target := 62, numerator := 1798407206222480549714329600 }, some { target := 63, numerator := 101434552789987470029619200 }, some { target := 64, numerator := 104176027189716861111500800 }, some { target := 65, numerator := 104176027189716861111500800 }, some { target := 66, numerator := 101434552789987470029619200 }, some { target := 67, numerator := 3144471136489611570918195200 }, some { target := 68, numerator := 101434552789987470029619200 }, some { target := 69, numerator := 131590771187010771930316800 }, some { target := 70, numerator := 134332245586740163012198400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 23079784965413869382428262400 }, some { target := 101, numerator := 17309838724060402036821196800 }, some { target := 102, numerator := 18271496430952646594422374400 }, some { target := 103, numerator := 23560613818859991661228851200 }, some { target := 104, numerator := 315423727860656214893186252800 }, some { target := 105, numerator := 551510694902702253784275353600 }, some { target := 106, numerator := 16829009870614279758020608000 }, some { target := 107, numerator := 315423727860656214893186252800 }, some { target := 108, numerator := 17790667577506524315621785600 }, some { target := 109, numerator := 18271496430952646594422374400 }, some { target := 110, numerator := 18271496430952646594422374400 }, some { target := 111, numerator := 17790667577506524315621785600 }, some { target := 112, numerator := 551510694902702253784275353600 }, some { target := 113, numerator := 17790667577506524315621785600 }, some { target := 114, numerator := 23079784965413869382428262400 }, some { target := 115, numerator := 23560613818859991661228851200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 23079787732425480438861004800 }, some { target := 316, numerator := 17309840799319110329145753600 }, some { target := 317, numerator := 18271498621503505347431628800 }, some { target := 318, numerator := 23560616643517677948003942400 }, some { target := 319, numerator := 315423765676481565997767065600 }, some { target := 320, numerator := 551510761022750542986949427200 }, some { target := 321, numerator := 16829011888226912820002816000 }, some { target := 322, numerator := 315423765676481565997767065600 }, some { target := 323, numerator := 17790669710411307838288691200 }, some { target := 324, numerator := 18271498621503505347431628800 }, some { target := 325, numerator := 18271498621503505347431628800 }, some { target := 326, numerator := 17790669710411307838288691200 }, some { target := 327, numerator := 551510761022750542986949427200 }, some { target := 328, numerator := 17790669710411307838288691200 }, some { target := 329, numerator := 23079787732425480438861004800 }, some { target := 330, numerator := 23560616643517677948003942400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 131588004175399715497574400 }, some { target := 654, numerator := 98691003131549786623180800 }, some { target := 655, numerator := 104173836638858108102246400 }, some { target := 656, numerator := 134329420929053876237107200 }, some { target := 657, numerator := 1798369390397129445133516800 }, some { target := 658, numerator := 3144405016441322368244121600 }, some { target := 659, numerator := 95949586377895625883648000 }, some { target := 660, numerator := 1798369390397129445133516800 }, some { target := 661, numerator := 101432419885203947362713600 }, some { target := 662, numerator := 104173836638858108102246400 }, some { target := 663, numerator := 104173836638858108102246400 }, some { target := 664, numerator := 101432419885203947362713600 }, some { target := 665, numerator := 3144405016441322368244121600 }, some { target := 666, numerator := 101432419885203947362713600 }, some { target := 667, numerator := 131588004175399715497574400 }, some { target := 668, numerator := 134329420929053876237107200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left6.expected ++ Left14.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left6.routed_eq, Left14.routed_eq]
  rfl

end Slot4

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14.Parent1
