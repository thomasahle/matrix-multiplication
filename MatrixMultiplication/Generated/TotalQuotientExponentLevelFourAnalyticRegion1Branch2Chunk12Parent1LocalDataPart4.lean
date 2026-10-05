import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 4, for region 1, branch 2,
parent 51; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 3, #[2199023255552, 2611340115968, 1992864825344, 20547123544064, 2473901162496, 1992864825344, 2473901162496, 2473901162496, 105965433126912, 2473901162496, 20547123544064, 105965433126912, 2199023255552, 2473901162496, 2473901162496, 2611340115968, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 10, numerator := 11333679558887148512870400 }, some { target := 11, numerator := 227126938360098456197922816 }, some { target := 12, numerator := 381264980360963675972960256 }, some { target := 13, numerator := 365851176160877153995456512 }, some { target := 14, numerator := 11333679558887148512870400 }, some { target := 15, numerator := 365851176160877153995456512 }, some { target := 16, numerator := 244354131289606921937485824 }, some { target := 17, numerator := 11787026741242634453385216 }, some { target := 18, numerator := 227126938360098456197922816 }, some { target := 19, numerator := 10880332376531662572355584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 24, numerator := 13458744476178488859033600 }, some { target := 25, numerator := 269713239302616916735033344 }, some { target := 26, numerator := 452752164178644365217890304 }, some { target := 27, numerator := 434448271691041620369604608 }, some { target := 28, numerator := 13458744476178488859033600 }, some { target := 29, numerator := 434448271691041620369604608 }, some { target := 30, numerator := 290170530906408219800764416 }, some { target := 31, numerator := 13997094255225628413394944 }, some { target := 32, numerator := 269713239302616916735033344 }, some { target := 33, numerator := 12920394697131349304672256 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 10271147100241478339788800 }, some { target := 56, numerator := 205833787888839225929367552 }, some { target := 57, numerator := 345521388452123331350495232 }, some { target := 58, numerator := 331552628395794920808382464 }, some { target := 59, numerator := 10271147100241478339788800 }, some { target := 60, numerator := 331552628395794920808382464 }, some { target := 61, numerator := 221445931481206273005846528 }, some { target := 62, numerator := 10681992984251137473380352 }, some { target := 63, numerator := 205833787888839225929367552 }, some { target := 64, numerator := 9860301216231819206197248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 69, numerator := 105899068378351793917132800 }, some { target := 70, numerator := 2122217330302169950099341312 }, some { target := 71, numerator := 3562444660247754347372347392 }, some { target := 72, numerator := 3418421927253195907645046784 }, some { target := 73, numerator := 105899068378351793917132800 }, some { target := 74, numerator := 3418421927253195907645046784 }, some { target := 75, numerator := 2283183914237264676853383168 }, some { target := 76, numerator := 110135031113485865673818112 }, some { target := 77, numerator := 2122217330302169950099341312 }, some { target := 78, numerator := 101663105643217722160447488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 95, numerator := 12750389503748042076979200 }, some { target := 96, numerator := 255517805655110763222663168 }, some { target := 97, numerator := 428923102906084135469580288 }, some { target := 98, numerator := 411582573180986798244888576 }, some { target := 99, numerator := 12750389503748042076979200 }, some { target := 100, numerator := 411582573180986798244888576 }, some { target := 101, numerator := 274898397700807787179671552 }, some { target := 102, numerator := 13260405083897963760058368 }, some { target := 103, numerator := 255517805655110763222663168 }, some { target := 104, numerator := 12240373923598120393900032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 144, numerator := 10271147100241478339788800 }, some { target := 145, numerator := 205833787888839225929367552 }, some { target := 146, numerator := 345521388452123331350495232 }, some { target := 147, numerator := 331552628395794920808382464 }, some { target := 148, numerator := 10271147100241478339788800 }, some { target := 149, numerator := 331552628395794920808382464 }, some { target := 150, numerator := 221445931481206273005846528 }, some { target := 151, numerator := 10681992984251137473380352 }, some { target := 152, numerator := 205833787888839225929367552 }, some { target := 153, numerator := 9860301216231819206197248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 170, numerator := 12750389503748042076979200 }, some { target := 171, numerator := 255517805655110763222663168 }, some { target := 172, numerator := 428923102906084135469580288 }, some { target := 173, numerator := 411582573180986798244888576 }, some { target := 174, numerator := 12750389503748042076979200 }, some { target := 175, numerator := 411582573180986798244888576 }, some { target := 176, numerator := 274898397700807787179671552 }, some { target := 177, numerator := 13260405083897963760058368 }, some { target := 178, numerator := 255517805655110763222663168 }, some { target := 179, numerator := 12240373923598120393900032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 271, numerator := 12750389503748042076979200 }, some { target := 272, numerator := 255517805655110763222663168 }, some { target := 273, numerator := 428923102906084135469580288 }, some { target := 274, numerator := 411582573180986798244888576 }, some { target := 275, numerator := 12750389503748042076979200 }, some { target := 276, numerator := 411582573180986798244888576 }, some { target := 277, numerator := 274898397700807787179671552 }, some { target := 278, numerator := 13260405083897963760058368 }, some { target := 279, numerator := 255517805655110763222663168 }, some { target := 280, numerator := 12240373923598120393900032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 285, numerator := 546141683743874468963942400 }, some { target := 286, numerator := 10944679342227244358037405696 }, some { target := 287, numerator := 18372206241143937135947022336 }, some { target := 288, numerator := 17629453551252267858156060672 }, some { target := 289, numerator := 546141683743874468963942400 }, some { target := 290, numerator := 17629453551252267858156060672 }, some { target := 291, numerator := 11774814701517933550862598144 }, some { target := 292, numerator := 567987351093629447722500096 }, some { target := 293, numerator := 10944679342227244358037405696 }, some { target := 294, numerator := 524296016394119490205384704 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 311, numerator := 12750389503748042076979200 }, some { target := 312, numerator := 255517805655110763222663168 }, some { target := 313, numerator := 428923102906084135469580288 }, some { target := 314, numerator := 411582573180986798244888576 }, some { target := 315, numerator := 12750389503748042076979200 }, some { target := 316, numerator := 411582573180986798244888576 }, some { target := 317, numerator := 274898397700807787179671552 }, some { target := 318, numerator := 13260405083897963760058368 }, some { target := 319, numerator := 255517805655110763222663168 }, some { target := 320, numerator := 12240373923598120393900032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 360, numerator := 105899068378351793917132800 }, some { target := 361, numerator := 2122217330302169950099341312 }, some { target := 362, numerator := 3562444660247754347372347392 }, some { target := 363, numerator := 3418421927253195907645046784 }, some { target := 364, numerator := 105899068378351793917132800 }, some { target := 365, numerator := 3418421927253195907645046784 }, some { target := 366, numerator := 2283183914237264676853383168 }, some { target := 367, numerator := 110135031113485865673818112 }, some { target := 368, numerator := 2122217330302169950099341312 }, some { target := 369, numerator := 101663105643217722160447488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 386, numerator := 546141683743874468963942400 }, some { target := 387, numerator := 10944679342227244358037405696 }, some { target := 388, numerator := 18372206241143937135947022336 }, some { target := 389, numerator := 17629453551252267858156060672 }, some { target := 390, numerator := 546141683743874468963942400 }, some { target := 391, numerator := 17629453551252267858156060672 }, some { target := 392, numerator := 11774814701517933550862598144 }, some { target := 393, numerator := 567987351093629447722500096 }, some { target := 394, numerator := 10944679342227244358037405696 }, some { target := 395, numerator := 524296016394119490205384704 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 11333679558887148512870400 }, some { target := 483, numerator := 227126938360098456197922816 }, some { target := 484, numerator := 381264980360963675972960256 }, some { target := 485, numerator := 365851176160877153995456512 }, some { target := 486, numerator := 11333679558887148512870400 }, some { target := 487, numerator := 365851176160877153995456512 }, some { target := 488, numerator := 244354131289606921937485824 }, some { target := 489, numerator := 11787026741242634453385216 }, some { target := 490, numerator := 227126938360098456197922816 }, some { target := 491, numerator := 10880332376531662572355584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 12750389503748042076979200 }, some { target := 628, numerator := 255517805655110763222663168 }, some { target := 629, numerator := 428923102906084135469580288 }, some { target := 630, numerator := 411582573180986798244888576 }, some { target := 631, numerator := 12750389503748042076979200 }, some { target := 632, numerator := 411582573180986798244888576 }, some { target := 633, numerator := 274898397700807787179671552 }, some { target := 634, numerator := 13260405083897963760058368 }, some { target := 635, numerator := 255517805655110763222663168 }, some { target := 636, numerator := 12240373923598120393900032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 12750389503748042076979200 }, some { target := 654, numerator := 255517805655110763222663168 }, some { target := 655, numerator := 428923102906084135469580288 }, some { target := 656, numerator := 411582573180986798244888576 }, some { target := 657, numerator := 12750389503748042076979200 }, some { target := 658, numerator := 411582573180986798244888576 }, some { target := 659, numerator := 274898397700807787179671552 }, some { target := 660, numerator := 13260405083897963760058368 }, some { target := 661, numerator := 255517805655110763222663168 }, some { target := 662, numerator := 12240373923598120393900032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 749, numerator := 13458744476178488859033600 }, some { target := 750, numerator := 269713239302616916735033344 }, some { target := 751, numerator := 452752164178644365217890304 }, some { target := 752, numerator := 434448271691041620369604608 }, some { target := 753, numerator := 13458744476178488859033600 }, some { target := 754, numerator := 434448271691041620369604608 }, some { target := 755, numerator := 290170530906408219800764416 }, some { target := 756, numerator := 13997094255225628413394944 }, some { target := 757, numerator := 269713239302616916735033344 }, some { target := 758, numerator := 12920394697131349304672256 }]

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

end Slot15

namespace Slot16

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨16, 1, #[50466754920448, 0, 0, 180541483646976, 0, 50466738143232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 3, 5]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1, numerator := 3710812420045939657366568960 }, some { target := 2, numerator := 3391751912901802789630377984 }, some { target := 3, numerator := 3710812420045939657366568960 }, some { target := 4, numerator := 3391751912901802789630377984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 13275186425336582085562859520 }, some { target := 52, numerator := 12133768527083343252037828608 }, some { target := 53, numerator := 13275186425336582085562859520 }, some { target := 54, numerator := 12133768527083343252037828608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 140, numerator := 3710811186419929728040304640 }, some { target := 141, numerator := 3391750785344571284134035456 }, some { target := 142, numerator := 3710811186419929728040304640 }, some { target := 143, numerator := 3391750785344571284134035456 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left3.expected ++ Left5.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left3.routed_eq, Left5.routed_eq]
  rfl

end Slot16

namespace Slot17

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨17, 1, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes

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
        8 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 0, numerator := 39614081257132168796771975168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 50, numerator := 39614081257132168796771975168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq]
  rfl

end Slot17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent1
