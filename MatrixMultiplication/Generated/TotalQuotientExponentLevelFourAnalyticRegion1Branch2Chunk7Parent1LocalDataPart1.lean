import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 31; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 588, #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416], #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 71, numerator := 35647631946168907534958592 }, some { target := 72, numerator := 5691044379531987065235308544 }, some { target := 74, numerator := 56788064710157343961229819904 }, some { target := 82, numerator := 5691044379531987065235308544 }, some { target := 89, numerator := 35643564439100654578827264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 950603518564504200932229120 }, some { target := 147, numerator := 151761183454186321739608227840 }, some { target := 149, numerator := 1514348392270862505632795197440 }, some { target := 157, numerator := 151761183454186321739608227840 }, some { target := 164, numerator := 950495051709350788768727040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 181, numerator := 909014614627307142141444096 }, some { target := 182, numerator := 145121631678065670163500367872 }, some { target := 184, numerator := 1448095650109012271011360407552 }, some { target := 192, numerator := 145121631678065670163500367872 }, some { target := 199, numerator := 908910893197066691760095232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 29706359955140756279132160 }, some { target := 243, numerator := 4742536982943322554362757120 }, some { target := 245, numerator := 47323387258464453301024849920 }, some { target := 253, numerator := 4742536982943322554362757120 }, some { target := 260, numerator := 29702970365917212149022720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 277, numerator := 932779702591419747164749824 }, some { target := 278, numerator := 148915661264420328206990573568 }, some { target := 280, numerator := 1485954359915783833652180287488 }, some { target := 288, numerator := 148915661264420328206990573568 }, some { target := 295, numerator := 932673269489800461479313408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 29706359955140756279132160 }, some { target := 313, numerator := 4742536982943322554362757120 }, some { target := 315, numerator := 47323387258464453301024849920 }, some { target := 323, numerator := 4742536982943322554362757120 }, some { target := 330, numerator := 29702970365917212149022720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 413, numerator := 909014614627307142141444096 }, some { target := 414, numerator := 145121631678065670163500367872 }, some { target := 416, numerator := 1448095650109012271011360407552 }, some { target := 424, numerator := 145121631678065670163500367872 }, some { target := 431, numerator := 908910893197066691760095232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 448, numerator := 516890663219449159256899584 }, some { target := 449, numerator := 82520143503213812445911973888 }, some { target := 451, numerator := 823426938297281487437832388608 }, some { target := 459, numerator := 82520143503213812445911973888 }, some { target := 466, numerator := 516831684366959491392995328 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 509, numerator := 932779702591419747164749824 }, some { target := 510, numerator := 148915661264420328206990573568 }, some { target := 512, numerator := 1485954359915783833652180287488 }, some { target := 520, numerator := 148915661264420328206990573568 }, some { target := 527, numerator := 932673269489800461479313408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 14562057650009998728030584832 }, some { target := 545, numerator := 2324791629038816716148623540224 }, some { target := 547, numerator := 23197924434099275008162381430784 }, some { target := 555, numerator := 2324791629038816716148623540224 }, some { target := 562, numerator := 14560396073372617395450937344 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 579, numerator := 570362111138702520559337472 }, some { target := 580, numerator := 91056710072511793043764936704 }, some { target := 582, numerator := 908609035362517503379677118464 }, some { target := 590, numerator := 91056710072511793043764936704 }, some { target := 597, numerator := 570297031025610473261236224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 950603518564504200932229120 }, some { target := 641, numerator := 151761183454186321739608227840 }, some { target := 643, numerator := 1514348392270862505632795197440 }, some { target := 651, numerator := 151761183454186321739608227840 }, some { target := 658, numerator := 950495051709350788768727040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 675, numerator := 909014614627307142141444096 }, some { target := 676, numerator := 145121631678065670163500367872 }, some { target := 678, numerator := 1448095650109012271011360407552 }, some { target := 686, numerator := 145121631678065670163500367872 }, some { target := 693, numerator := 908910893197066691760095232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 776, numerator := 29706359955140756279132160 }, some { target := 777, numerator := 4742536982943322554362757120 }, some { target := 779, numerator := 47323387258464453301024849920 }, some { target := 787, numerator := 4742536982943322554362757120 }, some { target := 794, numerator := 29702970365917212149022720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 811, numerator := 570362111138702520559337472 }, some { target := 812, numerator := 91056710072511793043764936704 }, some { target := 814, numerator := 908609035362517503379677118464 }, some { target := 822, numerator := 91056710072511793043764936704 }, some { target := 829, numerator := 570297031025610473261236224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 29706359955140756279132160 }, some { target := 847, numerator := 4742536982943322554362757120 }, some { target := 849, numerator := 47323387258464453301024849920 }, some { target := 857, numerator := 4742536982943322554362757120 }, some { target := 864, numerator := 29702970365917212149022720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 907, numerator := 914955886618335293397270528 }, some { target := 908, numerator := 146070139074654334674372919296 }, some { target := 910, numerator := 1457560327560705161671565377536 }, some { target := 918, numerator := 146070139074654334674372919296 }, some { target := 925, numerator := 914851487270250134189899776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 942, numerator := 516890663219449159256899584 }, some { target := 943, numerator := 82520143503213812445911973888 }, some { target := 945, numerator := 823426938297281487437832388608 }, some { target := 953, numerator := 82520143503213812445911973888 }, some { target := 960, numerator := 516831684366959491392995328 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 35647631946168907534958592 }, some { target := 1018, numerator := 5691044379531987065235308544 }, some { target := 1020, numerator := 56788064710157343961229819904 }, some { target := 1028, numerator := 5691044379531987065235308544 }, some { target := 1035, numerator := 35643564439100654578827264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected ++ Left16.expected ++ Left17.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq, Left16.routed_eq, Left17.routed_eq, Left18.routed_eq]
  rfl

end Slot4

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 23, #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0], #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

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
  [some { target := 29, numerator := 234607166868963974216417280 }, some { target := 30, numerator := 182472240898083091057213440 }, some { target := 31, numerator := 208539703883523532636815360 }, some { target := 32, numerator := 245034152063140150848258048 }, some { target := 33, numerator := 2893488391383889015335813120 }, some { target := 34, numerator := 6506438761165934218268639232 }, some { target := 35, numerator := 182472240898083091057213440 }, some { target := 36, numerator := 2893488391383889015335813120 }, some { target := 37, numerator := 208539703883523532636815360 }, some { target := 38, numerator := 203326211286435444320894976 }, some { target := 39, numerator := 203326211286435444320894976 }, some { target := 40, numerator := 203326211286435444320894976 }, some { target := 41, numerator := 6506438761165934218268639232 }, some { target := 42, numerator := 203326211286435444320894976 }, some { target := 43, numerator := 234607166868963974216417280 }, some { target := 44, numerator := 245034152063140150848258048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 229719517559193891420241920 }, some { target := 56, numerator := 178670735879373026660188160 }, some { target := 57, numerator := 204195126719283459040215040 }, some { target := 58, numerator := 239929273895158064372252672 }, some { target := 59, numerator := 2833207383230057994182983680 }, some { target := 60, numerator := 6370887953641643922054709248 }, some { target := 61, numerator := 178670735879373026660188160 }, some { target := 62, numerator := 2833207383230057994182983680 }, some { target := 63, numerator := 204195126719283459040215040 }, some { target := 64, numerator := 199090248551301372564209664 }, some { target := 65, numerator := 199090248551301372564209664 }, some { target := 66, numerator := 199090248551301372564209664 }, some { target := 67, numerator := 6370887953641643922054709248 }, some { target := 68, numerator := 199090248551301372564209664 }, some { target := 69, numerator := 229719517559193891420241920 }, some { target := 70, numerator := 239929273895158064372252672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 180843024461493063458488320 }, some { target := 105, numerator := 140655685692272382689935360 }, some { target := 106, numerator := 160749355076882723074211840 }, some { target := 107, numerator := 188880492215337199612198912 }, some { target := 108, numerator := 2230397301691747782654689280 }, some { target := 109, numerator := 5015379878398740959915409408 }, some { target := 110, numerator := 140655685692272382689935360 }, some { target := 111, numerator := 2230397301691747782654689280 }, some { target := 112, numerator := 160749355076882723074211840 }, some { target := 113, numerator := 156730621199960654997356544 }, some { target := 114, numerator := 156730621199960654997356544 }, some { target := 115, numerator := 156730621199960654997356544 }, some { target := 116, numerator := 5015379878398740959915409408 }, some { target := 117, numerator := 156730621199960654997356544 }, some { target := 118, numerator := 180843024461493063458488320 }, some { target := 119, numerator := 188880492215337199612198912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 130, numerator := 5684336147262606291951943680 }, some { target := 131, numerator := 4421150336759804893740400640 }, some { target := 132, numerator := 5052743242011205592846172160 }, some { target := 133, numerator := 5936973309363166571594252288 }, some { target := 134, numerator := 70106812482905477600740638720 }, some { target := 135, numerator := 157645589150749614496800571392 }, some { target := 136, numerator := 4421150336759804893740400640 }, some { target := 137, numerator := 70106812482905477600740638720 }, some { target := 138, numerator := 5052743242011205592846172160 }, some { target := 139, numerator := 4926424660960925453025017856 }, some { target := 140, numerator := 4926424660960925453025017856 }, some { target := 141, numerator := 4926424660960925453025017856 }, some { target := 142, numerator := 157645589150749614496800571392 }, some { target := 143, numerator := 4926424660960925453025017856 }, some { target := 144, numerator := 5684336147262606291951943680 }, some { target := 145, numerator := 5936973309363166571594252288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 165, numerator := 180843024461493063458488320 }, some { target := 166, numerator := 140655685692272382689935360 }, some { target := 167, numerator := 160749355076882723074211840 }, some { target := 168, numerator := 188880492215337199612198912 }, some { target := 169, numerator := 2230397301691747782654689280 }, some { target := 170, numerator := 5015379878398740959915409408 }, some { target := 171, numerator := 140655685692272382689935360 }, some { target := 172, numerator := 2230397301691747782654689280 }, some { target := 173, numerator := 160749355076882723074211840 }, some { target := 174, numerator := 156730621199960654997356544 }, some { target := 175, numerator := 156730621199960654997356544 }, some { target := 176, numerator := 156730621199960654997356544 }, some { target := 177, numerator := 5015379878398740959915409408 }, some { target := 178, numerator := 156730621199960654997356544 }, some { target := 179, numerator := 180843024461493063458488320 }, some { target := 180, numerator := 188880492215337199612198912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 180843024461493063458488320 }, some { target := 227, numerator := 140655685692272382689935360 }, some { target := 228, numerator := 160749355076882723074211840 }, some { target := 229, numerator := 188880492215337199612198912 }, some { target := 230, numerator := 2230397301691747782654689280 }, some { target := 231, numerator := 5015379878398740959915409408 }, some { target := 232, numerator := 140655685692272382689935360 }, some { target := 233, numerator := 2230397301691747782654689280 }, some { target := 234, numerator := 160749355076882723074211840 }, some { target := 235, numerator := 156730621199960654997356544 }, some { target := 236, numerator := 156730621199960654997356544 }, some { target := 237, numerator := 156730621199960654997356544 }, some { target := 238, numerator := 5015379878398740959915409408 }, some { target := 239, numerator := 156730621199960654997356544 }, some { target := 240, numerator := 180843024461493063458488320 }, some { target := 241, numerator := 188880492215337199612198912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 261, numerator := 185730673771263146254663680 }, some { target := 262, numerator := 144457190710982447086960640 }, some { target := 263, numerator := 165093932241122796670812160 }, some { target := 264, numerator := 193985370383319286088204288 }, some { target := 265, numerator := 2290678309845578803807518720 }, some { target := 266, numerator := 5150930685923031256129339392 }, some { target := 267, numerator := 144457190710982447086960640 }, some { target := 268, numerator := 2290678309845578803807518720 }, some { target := 269, numerator := 165093932241122796670812160 }, some { target := 270, numerator := 160966583935094726754041856 }, some { target := 271, numerator := 160966583935094726754041856 }, some { target := 272, numerator := 160966583935094726754041856 }, some { target := 273, numerator := 5150930685923031256129339392 }, some { target := 274, numerator := 160966583935094726754041856 }, some { target := 275, numerator := 185730673771263146254663680 }, some { target := 276, numerator := 193985370383319286088204288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 371, numerator := 185730673771263146254663680 }, some { target := 372, numerator := 144457190710982447086960640 }, some { target := 373, numerator := 165093932241122796670812160 }, some { target := 374, numerator := 193985370383319286088204288 }, some { target := 375, numerator := 2290678309845578803807518720 }, some { target := 376, numerator := 5150930685923031256129339392 }, some { target := 377, numerator := 144457190710982447086960640 }, some { target := 378, numerator := 2290678309845578803807518720 }, some { target := 379, numerator := 165093932241122796670812160 }, some { target := 380, numerator := 160966583935094726754041856 }, some { target := 381, numerator := 160966583935094726754041856 }, some { target := 382, numerator := 160966583935094726754041856 }, some { target := 383, numerator := 5150930685923031256129339392 }, some { target := 384, numerator := 160966583935094726754041856 }, some { target := 385, numerator := 185730673771263146254663680 }, some { target := 386, numerator := 193985370383319286088204288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 397, numerator := 3142758506182163237940756480 }, some { target := 398, numerator := 2444367727030571407287255040 }, some { target := 399, numerator := 2793563116606367322614005760 }, some { target := 400, numerator := 3282436662012481604071456768 }, some { target := 401, numerator := 38760688242913346601269329920 }, some { target := 402, numerator := 87159169238118660465556979712 }, some { target := 403, numerator := 2444367727030571407287255040 }, some { target := 404, numerator := 38760688242913346601269329920 }, some { target := 405, numerator := 2793563116606367322614005760 }, some { target := 406, numerator := 2723724038691208139548655616 }, some { target := 407, numerator := 2723724038691208139548655616 }, some { target := 408, numerator := 2723724038691208139548655616 }, some { target := 409, numerator := 87159169238118660465556979712 }, some { target := 410, numerator := 2723724038691208139548655616 }, some { target := 411, numerator := 3142758506182163237940756480 }, some { target := 412, numerator := 3282436662012481604071456768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 432, numerator := 171067725841952897866137600 }, some { target := 433, numerator := 133052675654852253895884800 }, some { target := 434, numerator := 152060200748402575881011200 }, some { target := 435, numerator := 178670735879373026660188160 }, some { target := 436, numerator := 2109835285384085740349030400 }, some { target := 437, numerator := 4744278263350160367487549440 }, some { target := 438, numerator := 133052675654852253895884800 }, some { target := 439, numerator := 2109835285384085740349030400 }, some { target := 440, numerator := 152060200748402575881011200 }, some { target := 441, numerator := 148258695729692511483985920 }, some { target := 442, numerator := 148258695729692511483985920 }, some { target := 443, numerator := 148258695729692511483985920 }, some { target := 444, numerator := 4744278263350160367487549440 }, some { target := 445, numerator := 148258695729692511483985920 }, some { target := 446, numerator := 171067725841952897866137600 }, some { target := 447, numerator := 178670735879373026660188160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 493, numerator := 5684336147262606291951943680 }, some { target := 494, numerator := 4421150336759804893740400640 }, some { target := 495, numerator := 5052743242011205592846172160 }, some { target := 496, numerator := 5936973309363166571594252288 }, some { target := 497, numerator := 70106812482905477600740638720 }, some { target := 498, numerator := 157645589150749614496800571392 }, some { target := 499, numerator := 4421150336759804893740400640 }, some { target := 500, numerator := 70106812482905477600740638720 }, some { target := 501, numerator := 5052743242011205592846172160 }, some { target := 502, numerator := 4926424660960925453025017856 }, some { target := 503, numerator := 4926424660960925453025017856 }, some { target := 504, numerator := 4926424660960925453025017856 }, some { target := 505, numerator := 157645589150749614496800571392 }, some { target := 506, numerator := 4926424660960925453025017856 }, some { target := 507, numerator := 5684336147262606291951943680 }, some { target := 508, numerator := 5936973309363166571594252288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 528, numerator := 3142758506182163237940756480 }, some { target := 529, numerator := 2444367727030571407287255040 }, some { target := 530, numerator := 2793563116606367322614005760 }, some { target := 531, numerator := 3282436662012481604071456768 }, some { target := 532, numerator := 38760688242913346601269329920 }, some { target := 533, numerator := 87159169238118660465556979712 }, some { target := 534, numerator := 2444367727030571407287255040 }, some { target := 535, numerator := 38760688242913346601269329920 }, some { target := 536, numerator := 2793563116606367322614005760 }, some { target := 537, numerator := 2723724038691208139548655616 }, some { target := 538, numerator := 2723724038691208139548655616 }, some { target := 539, numerator := 2723724038691208139548655616 }, some { target := 540, numerator := 87159169238118660465556979712 }, some { target := 541, numerator := 2723724038691208139548655616 }, some { target := 542, numerator := 3142758506182163237940756480 }, some { target := 543, numerator := 3282436662012481604071456768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 234607166868963974216417280 }, some { target := 625, numerator := 182472240898083091057213440 }, some { target := 626, numerator := 208539703883523532636815360 }, some { target := 627, numerator := 245034152063140150848258048 }, some { target := 628, numerator := 2893488391383889015335813120 }, some { target := 629, numerator := 6506438761165934218268639232 }, some { target := 630, numerator := 182472240898083091057213440 }, some { target := 631, numerator := 2893488391383889015335813120 }, some { target := 632, numerator := 208539703883523532636815360 }, some { target := 633, numerator := 203326211286435444320894976 }, some { target := 634, numerator := 203326211286435444320894976 }, some { target := 635, numerator := 203326211286435444320894976 }, some { target := 636, numerator := 6506438761165934218268639232 }, some { target := 637, numerator := 203326211286435444320894976 }, some { target := 638, numerator := 234607166868963974216417280 }, some { target := 639, numerator := 245034152063140150848258048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 760, numerator := 180843024461493063458488320 }, some { target := 761, numerator := 140655685692272382689935360 }, some { target := 762, numerator := 160749355076882723074211840 }, some { target := 763, numerator := 188880492215337199612198912 }, some { target := 764, numerator := 2230397301691747782654689280 }, some { target := 765, numerator := 5015379878398740959915409408 }, some { target := 766, numerator := 140655685692272382689935360 }, some { target := 767, numerator := 2230397301691747782654689280 }, some { target := 768, numerator := 160749355076882723074211840 }, some { target := 769, numerator := 156730621199960654997356544 }, some { target := 770, numerator := 156730621199960654997356544 }, some { target := 771, numerator := 156730621199960654997356544 }, some { target := 772, numerator := 5015379878398740959915409408 }, some { target := 773, numerator := 156730621199960654997356544 }, some { target := 774, numerator := 180843024461493063458488320 }, some { target := 775, numerator := 188880492215337199612198912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 795, numerator := 171067725841952897866137600 }, some { target := 796, numerator := 133052675654852253895884800 }, some { target := 797, numerator := 152060200748402575881011200 }, some { target := 798, numerator := 178670735879373026660188160 }, some { target := 799, numerator := 2109835285384085740349030400 }, some { target := 800, numerator := 4744278263350160367487549440 }, some { target := 801, numerator := 133052675654852253895884800 }, some { target := 802, numerator := 2109835285384085740349030400 }, some { target := 803, numerator := 152060200748402575881011200 }, some { target := 804, numerator := 148258695729692511483985920 }, some { target := 805, numerator := 148258695729692511483985920 }, some { target := 806, numerator := 148258695729692511483985920 }, some { target := 807, numerator := 4744278263350160367487549440 }, some { target := 808, numerator := 148258695729692511483985920 }, some { target := 809, numerator := 171067725841952897866137600 }, some { target := 810, numerator := 178670735879373026660188160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 891, numerator := 229719517559193891420241920 }, some { target := 892, numerator := 178670735879373026660188160 }, some { target := 893, numerator := 204195126719283459040215040 }, some { target := 894, numerator := 239929273895158064372252672 }, some { target := 895, numerator := 2833207383230057994182983680 }, some { target := 896, numerator := 6370887953641643922054709248 }, some { target := 897, numerator := 178670735879373026660188160 }, some { target := 898, numerator := 2833207383230057994182983680 }, some { target := 899, numerator := 204195126719283459040215040 }, some { target := 900, numerator := 199090248551301372564209664 }, some { target := 901, numerator := 199090248551301372564209664 }, some { target := 902, numerator := 199090248551301372564209664 }, some { target := 903, numerator := 6370887953641643922054709248 }, some { target := 904, numerator := 199090248551301372564209664 }, some { target := 905, numerator := 229719517559193891420241920 }, some { target := 906, numerator := 239929273895158064372252672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq]
  rfl

end Slot5

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent1
