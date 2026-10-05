import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk9Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 40; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 53, #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0], #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 55, numerator := 272235809649188110388428800 }, some { target := 56, numerator := 211738963060479641413222400 }, some { target := 57, numerator := 241987386354833875900825600 }, some { target := 58, numerator := 284335178966929804183470080 }, some { target := 59, numerator := 3357574985673320028123955200 }, some { target := 60, numerator := 7550006454270816928105758720 }, some { target := 61, numerator := 211738963060479641413222400 }, some { target := 62, numerator := 3357574985673320028123955200 }, some { target := 63, numerator := 241987386354833875900825600 }, some { target := 64, numerator := 235937701695963029003304960 }, some { target := 65, numerator := 235937701695963029003304960 }, some { target := 66, numerator := 235937701695963029003304960 }, some { target := 67, numerator := 7550006454270816928105758720 }, some { target := 68, numerator := 235937701695963029003304960 }, some { target := 69, numerator := 272235809649188110388428800 }, some { target := 70, numerator := 284335178966929804183470080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 22794068828597936543005409280 }, some { target := 101, numerator := 17728720200020617311226429440 }, some { target := 102, numerator := 20261394514309276927115919360 }, some { target := 103, numerator := 23807138554313400389361205248 }, some { target := 104, numerator := 281126848886041217363733381120 }, some { target := 105, numerator := 632155508846449440126016684032 }, some { target := 106, numerator := 17728720200020617311226429440 }, some { target := 107, numerator := 281126848886041217363733381120 }, some { target := 108, numerator := 20261394514309276927115919360 }, some { target := 109, numerator := 19754859651451545003938021376 }, some { target := 110, numerator := 19754859651451545003938021376 }, some { target := 111, numerator := 19754859651451545003938021376 }, some { target := 112, numerator := 632155508846449440126016684032 }, some { target := 113, numerator := 19754859651451545003938021376 }, some { target := 114, numerator := 22794068828597936543005409280 }, some { target := 115, numerator := 23807138554313400389361205248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 22794077077751302004995522560 }, some { target := 316, numerator := 17728726616028790448329850880 }, some { target := 317, numerator := 20261401846890046226662686720 }, some { target := 318, numerator := 23807147170095804316328656896 }, some { target := 319, numerator := 281126950625599391394944778240 }, some { target := 320, numerator := 632155737622969442271875825664 }, some { target := 321, numerator := 17728726616028790448329850880 }, some { target := 322, numerator := 281126950625599391394944778240 }, some { target := 323, numerator := 20261401846890046226662686720 }, some { target := 324, numerator := 19754866800717795070996119552 }, some { target := 325, numerator := 19754866800717795070996119552 }, some { target := 326, numerator := 19754866800717795070996119552 }, some { target := 327, numerator := 632155737622969442271875825664 }, some { target := 328, numerator := 19754866800717795070996119552 }, some { target := 329, numerator := 22794077077751302004995522560 }, some { target := 330, numerator := 23807147170095804316328656896 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 272227560495822648398315520 }, some { target := 654, numerator := 211732547052306504309800960 }, some { target := 655, numerator := 241980053774064576354058240 }, some { target := 656, numerator := 284326563184525877216018432 }, some { target := 657, numerator := 3357473246115145996912558080 }, some { target := 658, numerator := 7549777677750814782246617088 }, some { target := 659, numerator := 211732547052306504309800960 }, some { target := 660, numerator := 3357473246115145996912558080 }, some { target := 661, numerator := 241980053774064576354058240 }, some { target := 662, numerator := 235930552429712961945206784 }, some { target := 663, numerator := 235930552429712961945206784 }, some { target := 664, numerator := 235930552429712961945206784 }, some { target := 665, numerator := 7549777677750814782246617088 }, some { target := 666, numerator := 235930552429712961945206784 }, some { target := 667, numerator := 272227560495822648398315520 }, some { target := 668, numerator := 284326563184525877216018432 }]

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

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 42, #[2130303778816, 50989851738112, 38139309588480, 44255343017984, 2130303778816, 44186623541248, 44392781971456, 2130303778816, 50989851738112, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[153243090944, 22633202581504, 0, 235902085365760, 0, 0, 0, 0, 0, 0, 0, 22633202581504, 0, 0, 0, 0, 0, 0, 153243090944]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

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
  [some { target := 142, numerator := 13711082100048780242976768 }, some { target := 143, numerator := 2025055073415612732002009088 }, some { target := 145, numerator := 21106810363180631942989086720 }, some { target := 153, numerator := 2025055073415612732002009088 }, some { target := 160, numerator := 13711082100048780242976768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 282, numerator := 328181384459232094848024576 }, some { target := 283, numerator := 48470673047560795069209378816 }, some { target := 285, numerator := 505201719015484803280577495040 }, some { target := 293, numerator := 48470673047560795069209378816 }, some { target := 300, numerator := 328181384459232094848024576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 245472598887970097898455040 }, some { target := 358, numerator := 36255018249860163427777904640 }, some { target := 360, numerator := 377879991985975829947062681600 }, some { target := 368, numerator := 36255018249860163427777904640 }, some { target := 375, numerator := 245472598887970097898455040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 284836673304239176660549632 }, some { target := 393, numerator := 42068886041279180626106253312 }, some { target := 395, numerator := 438476963673816999073708769280 }, some { target := 403, numerator := 42068886041279180626106253312 }, some { target := 410, numerator := 284836673304239176660549632 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 498, numerator := 13711082100048780242976768 }, some { target := 499, numerator := 2025055073415612732002009088 }, some { target := 501, numerator := 21106810363180631942989086720 }, some { target := 509, numerator := 2025055073415612732002009088 }, some { target := 516, numerator := 13711082100048780242976768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 284394380333269861168840704 }, some { target := 574, numerator := 42003561684072225376686833664 }, some { target := 576, numerator := 437796098823391817398128476160 }, some { target := 584, numerator := 42003561684072225376686833664 }, some { target := 591, numerator := 284394380333269861168840704 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 608, numerator := 285721259246177807643967488 }, some { target := 609, numerator := 42199534755693091124945092608 }, some { target := 611, numerator := 439838693374667362424869355520 }, some { target := 619, numerator := 42199534755693091124945092608 }, some { target := 626, numerator := 285721259246177807643967488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 13711082100048780242976768 }, some { target := 670, numerator := 2025055073415612732002009088 }, some { target := 672, numerator := 21106810363180631942989086720 }, some { target := 680, numerator := 2025055073415612732002009088 }, some { target := 687, numerator := 13711082100048780242976768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 704, numerator := 328181384459232094848024576 }, some { target := 705, numerator := 48470673047560795069209378816 }, some { target := 707, numerator := 505201719015484803280577495040 }, some { target := 715, numerator := 48470673047560795069209378816 }, some { target := 722, numerator := 328181384459232094848024576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 739, numerator := 13711082100048780242976768 }, some { target := 740, numerator := 2025055073415612732002009088 }, some { target := 742, numerator := 21106810363180631942989086720 }, some { target := 750, numerator := 2025055073415612732002009088 }, some { target := 757, numerator := 13711082100048780242976768 }]

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

end Slot6

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 114, #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0], #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0]⟩

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
  [some { target := 55, numerator := 311871102294426692263870464 }, some { target := 56, numerator := 26225004556276223360869859328 }, some { target := 61, numerator := 26224998229392035049614868480 }, some { target := 69, numerator := 311877429178615003518861312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 26225004556276223360869859328 }, some { target := 101, numerator := 2205240751441686748001998995456 }, some { target := 106, numerator := 2205240219418791889173699624960 }, some { target := 114, numerator := 26225536579171082189169229824 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 26224998229392035049614868480 }, some { target := 316, numerator := 2205240219418791889173699624960 }, some { target := 321, numerator := 2205239687396025382934780313600 }, some { target := 329, numerator := 26225530252158541288534179840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 311877429178615003518861312 }, some { target := 654, numerator := 26225536579171082189169229824 }, some { target := 659, numerator := 26225530252158541288534179840 }, some { target := 667, numerator := 311883756191155904153911296 }]

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

end Slot7

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 43, #[153243090944, 22633202581504, 0, 235902085365760, 0, 0, 0, 0, 0, 0, 0, 22633202581504, 0, 0, 0, 0, 0, 0, 153243090944], #[2130303778816, 50989851738112, 38139309588480, 44255343017984, 2130303778816, 44186623541248, 44392781971456, 2130303778816, 50989851738112, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 3, 11, 18]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 11, numerator := 14037536435764227391619072 }, some { target := 12, numerator := 335995226946356668534882304 }, some { target := 13, numerator := 251317184575778909753180160 }, some { target := 14, numerator := 291618498859102014200086528 }, some { target := 15, numerator := 14037536435764227391619072 }, some { target := 16, numerator := 291165675103109619768098816 }, some { target := 17, numerator := 292524146371086803064061952 }, some { target := 18, numerator := 14037536435764227391619072 }, some { target := 19, numerator := 335995226946356668534882304 }, some { target := 20, numerator := 14037536435764227391619072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 31, numerator := 2073270670401698749430628352 }, some { target := 32, numerator := 49624736691550337808952459264 }, some { target := 33, numerator := 37118232970094929223677378560 }, some { target := 34, numerator := 43070526185119161117204021248 }, some { target := 35, numerator := 2073270670401698749430628352 }, some { target := 36, numerator := 43003646486073945028512710656 }, some { target := 37, numerator := 43204285583209593294586642432 }, some { target := 38, numerator := 2073270670401698749430628352 }, some { target := 39, numerator := 49624736691550337808952459264 }, some { target := 40, numerator := 2073270670401698749430628352 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 76, numerator := 21609353467065885084488826880 }, some { target := 77, numerator := 517230331372996346215829340160 }, some { target := 78, numerator := 386877134652308587802945126400 }, some { target := 79, numerator := 448916891380336451432606597120 }, some { target := 80, numerator := 21609353467065885084488826880 }, some { target := 81, numerator := 448219815462044003526655344640 }, some { target := 82, numerator := 450311043216921347244509102080 }, some { target := 83, numerator := 21609353467065885084488826880 }, some { target := 84, numerator := 517230331372996346215829340160 }, some { target := 85, numerator := 21609353467065885084488826880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 305, numerator := 2073270670401698749430628352 }, some { target := 306, numerator := 49624736691550337808952459264 }, some { target := 307, numerator := 37118232970094929223677378560 }, some { target := 308, numerator := 43070526185119161117204021248 }, some { target := 309, numerator := 2073270670401698749430628352 }, some { target := 310, numerator := 43003646486073945028512710656 }, some { target := 311, numerator := 43204285583209593294586642432 }, some { target := 312, numerator := 2073270670401698749430628352 }, some { target := 313, numerator := 49624736691550337808952459264 }, some { target := 314, numerator := 2073270670401698749430628352 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 643, numerator := 14037536435764227391619072 }, some { target := 644, numerator := 335995226946356668534882304 }, some { target := 645, numerator := 251317184575778909753180160 }, some { target := 646, numerator := 291618498859102014200086528 }, some { target := 647, numerator := 14037536435764227391619072 }, some { target := 648, numerator := 291165675103109619768098816 }, some { target := 649, numerator := 292524146371086803064061952 }, some { target := 650, numerator := 14037536435764227391619072 }, some { target := 651, numerator := 335995226946356668534882304 }, some { target := 652, numerator := 14037536435764227391619072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left3.expected ++ Left11.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left3.routed_eq, Left11.routed_eq, Left18.routed_eq]
  rfl

end Slot8

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent2
