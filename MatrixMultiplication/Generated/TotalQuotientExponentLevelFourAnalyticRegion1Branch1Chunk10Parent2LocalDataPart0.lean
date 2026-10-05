import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 44; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 7, #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 26, numerator := 4760145414732602375405568 }, some { target := 27, numerator := 71402181220989035631083520 }, some { target := 28, numerator := 125350495921291862552346624 }, some { target := 29, numerator := 4760145414732602375405568 }, some { target := 30, numerator := 79335756912210039590092800 }, some { target := 31, numerator := 4760145414732602375405568 }, some { target := 32, numerator := 125350495921291862552346624 }, some { target := 33, numerator := 124557138352169762156445696 }, some { target := 34, numerator := 79335756912210039590092800 }, some { target := 35, numerator := 1922305389982849259267948544 }, some { target := 36, numerator := 122970423213925561364643840 }, some { target := 37, numerator := 71402181220989035631083520 }, some { target := 38, numerator := 125350495921291862552346624 }, some { target := 39, numerator := 4760145414732602375405568 }, some { target := 40, numerator := 122970423213925561364643840 }, some { target := 41, numerator := 4760145414732602375405568 }, some { target := 42, numerator := 125350495921291862552346624 }, some { target := 43, numerator := 125350495921291862552346624 }, some { target := 44, numerator := 4760145414732602375405568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 61, numerator := 99368035532543074586591232 }, some { target := 62, numerator := 1490520532988146118798868480 }, some { target := 63, numerator := 2616691602356967630780235776 }, some { target := 64, numerator := 99368035532543074586591232 }, some { target := 65, numerator := 1656133925542384576443187200 }, some { target := 66, numerator := 99368035532543074586591232 }, some { target := 67, numerator := 2616691602356967630780235776 }, some { target := 68, numerator := 2600130263101543785015803904 }, some { target := 69, numerator := 1656133925542384576443187200 }, some { target := 70, numerator := 40128125015891978287218425856 }, some { target := 71, numerator := 2567007584590696093486940160 }, some { target := 72, numerator := 1490520532988146118798868480 }, some { target := 73, numerator := 2616691602356967630780235776 }, some { target := 74, numerator := 99368035532543074586591232 }, some { target := 75, numerator := 2567007584590696093486940160 }, some { target := 76, numerator := 99368035532543074586591232 }, some { target := 77, numerator := 2616691602356967630780235776 }, some { target := 78, numerator := 2616691602356967630780235776 }, some { target := 79, numerator := 99368035532543074586591232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 96, numerator := 5156824199293652573356032 }, some { target := 97, numerator := 77352362989404788600340480 }, some { target := 98, numerator := 135796370581399517765042176 }, some { target := 99, numerator := 5156824199293652573356032 }, some { target := 100, numerator := 85947069988227542889267200 }, some { target := 101, numerator := 5156824199293652573356032 }, some { target := 102, numerator := 135796370581399517765042176 }, some { target := 103, numerator := 134936899881517242336149504 }, some { target := 104, numerator := 85947069988227542889267200 }, some { target := 105, numerator := 2082497505814753364206944256 }, some { target := 106, numerator := 133217958481752691478364160 }, some { target := 107, numerator := 77352362989404788600340480 }, some { target := 108, numerator := 135796370581399517765042176 }, some { target := 109, numerator := 5156824199293652573356032 }, some { target := 110, numerator := 133217958481752691478364160 }, some { target := 111, numerator := 5156824199293652573356032 }, some { target := 112, numerator := 135796370581399517765042176 }, some { target := 113, numerator := 135796370581399517765042176 }, some { target := 114, numerator := 5156824199293652573356032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 106904932439203028347650048 }, some { target := 158, numerator := 1603573986588045425214750720 }, some { target := 159, numerator := 2815163220899013079821451264 }, some { target := 160, numerator := 106904932439203028347650048 }, some { target := 161, numerator := 1781748873986717139127500800 }, some { target := 162, numerator := 106904932439203028347650048 }, some { target := 163, numerator := 2815163220899013079821451264 }, some { target := 164, numerator := 2797345732159145908430176256 }, some { target := 165, numerator := 1781748873986717139127500800 }, some { target := 166, numerator := 43171775216698156281059344384 }, some { target := 167, numerator := 2761710754679411565647626240 }, some { target := 168, numerator := 1603573986588045425214750720 }, some { target := 169, numerator := 2815163220899013079821451264 }, some { target := 170, numerator := 106904932439203028347650048 }, some { target := 171, numerator := 2761710754679411565647626240 }, some { target := 172, numerator := 106904932439203028347650048 }, some { target := 173, numerator := 2815163220899013079821451264 }, some { target := 174, numerator := 2815163220899013079821451264 }, some { target := 175, numerator := 106904932439203028347650048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 192, numerator := 160059889570383754873012224 }, some { target := 193, numerator := 2400898343555756323095183360 }, some { target := 194, numerator := 4214910425353438878322655232 }, some { target := 195, numerator := 160059889570383754873012224 }, some { target := 196, numerator := 2667664826173062581216870400 }, some { target := 197, numerator := 160059889570383754873012224 }, some { target := 198, numerator := 4214910425353438878322655232 }, some { target := 199, numerator := 4188233777091708252510486528 }, some { target := 200, numerator := 2667664826173062581216870400 }, some { target := 201, numerator := 64637518738173306342884769792 }, some { target := 202, numerator := 4134880480568247000886149120 }, some { target := 203, numerator := 2400898343555756323095183360 }, some { target := 204, numerator := 4214910425353438878322655232 }, some { target := 205, numerator := 160059889570383754873012224 }, some { target := 206, numerator := 4134880480568247000886149120 }, some { target := 207, numerator := 160059889570383754873012224 }, some { target := 208, numerator := 4214910425353438878322655232 }, some { target := 209, numerator := 4214910425353438878322655232 }, some { target := 210, numerator := 160059889570383754873012224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 4958484807013127474380800 }, some { target := 268, numerator := 74377272105196912115712000 }, some { target := 269, numerator := 130573433251345690158694400 }, some { target := 270, numerator := 4958484807013127474380800 }, some { target := 271, numerator := 82641413450218791239680000 }, some { target := 272, numerator := 4958484807013127474380800 }, some { target := 273, numerator := 130573433251345690158694400 }, some { target := 274, numerator := 129747019116843502246297600 }, some { target := 275, numerator := 82641413450218791239680000 }, some { target := 276, numerator := 2002401447898801311737446400 }, some { target := 277, numerator := 128094190847839126421504000 }, some { target := 278, numerator := 74377272105196912115712000 }, some { target := 279, numerator := 130573433251345690158694400 }, some { target := 280, numerator := 4958484807013127474380800 }, some { target := 281, numerator := 128094190847839126421504000 }, some { target := 282, numerator := 4958484807013127474380800 }, some { target := 283, numerator := 130573433251345690158694400 }, some { target := 284, numerator := 130573433251345690158694400 }, some { target := 285, numerator := 4958484807013127474380800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 373, numerator := 160059889570383754873012224 }, some { target := 374, numerator := 2400898343555756323095183360 }, some { target := 375, numerator := 4214910425353438878322655232 }, some { target := 376, numerator := 160059889570383754873012224 }, some { target := 377, numerator := 2667664826173062581216870400 }, some { target := 378, numerator := 160059889570383754873012224 }, some { target := 379, numerator := 4214910425353438878322655232 }, some { target := 380, numerator := 4188233777091708252510486528 }, some { target := 381, numerator := 2667664826173062581216870400 }, some { target := 382, numerator := 64637518738173306342884769792 }, some { target := 383, numerator := 4134880480568247000886149120 }, some { target := 384, numerator := 2400898343555756323095183360 }, some { target := 385, numerator := 4214910425353438878322655232 }, some { target := 386, numerator := 160059889570383754873012224 }, some { target := 387, numerator := 4134880480568247000886149120 }, some { target := 388, numerator := 160059889570383754873012224 }, some { target := 389, numerator := 4214910425353438878322655232 }, some { target := 390, numerator := 4214910425353438878322655232 }, some { target := 391, numerator := 160059889570383754873012224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 408, numerator := 166803428907921608238170112 }, some { target := 409, numerator := 2502051433618824123572551680 }, some { target := 410, numerator := 4392490294575269016938479616 }, some { target := 411, numerator := 166803428907921608238170112 }, some { target := 412, numerator := 2780057148465360137302835200 }, some { target := 413, numerator := 166803428907921608238170112 }, some { target := 414, numerator := 4392490294575269016938479616 }, some { target := 415, numerator := 4364689723090615415565451264 }, some { target := 416, numerator := 2780057148465360137302835200 }, some { target := 417, numerator := 67360784707315676126847696896 }, some { target := 418, numerator := 4309088580121308212819394560 }, some { target := 419, numerator := 2502051433618824123572551680 }, some { target := 420, numerator := 4392490294575269016938479616 }, some { target := 421, numerator := 166803428907921608238170112 }, some { target := 422, numerator := 4309088580121308212819394560 }, some { target := 423, numerator := 166803428907921608238170112 }, some { target := 424, numerator := 4392490294575269016938479616 }, some { target := 425, numerator := 4392490294575269016938479616 }, some { target := 426, numerator := 166803428907921608238170112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 483, numerator := 99368035532543074586591232 }, some { target := 484, numerator := 1490520532988146118798868480 }, some { target := 485, numerator := 2616691602356967630780235776 }, some { target := 486, numerator := 99368035532543074586591232 }, some { target := 487, numerator := 1656133925542384576443187200 }, some { target := 488, numerator := 99368035532543074586591232 }, some { target := 489, numerator := 2616691602356967630780235776 }, some { target := 490, numerator := 2600130263101543785015803904 }, some { target := 491, numerator := 1656133925542384576443187200 }, some { target := 492, numerator := 40128125015891978287218425856 }, some { target := 493, numerator := 2567007584590696093486940160 }, some { target := 494, numerator := 1490520532988146118798868480 }, some { target := 495, numerator := 2616691602356967630780235776 }, some { target := 496, numerator := 99368035532543074586591232 }, some { target := 497, numerator := 2567007584590696093486940160 }, some { target := 498, numerator := 99368035532543074586591232 }, some { target := 499, numerator := 2616691602356967630780235776 }, some { target := 500, numerator := 2616691602356967630780235776 }, some { target := 501, numerator := 99368035532543074586591232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 623, numerator := 4958484807013127474380800 }, some { target := 624, numerator := 74377272105196912115712000 }, some { target := 625, numerator := 130573433251345690158694400 }, some { target := 626, numerator := 4958484807013127474380800 }, some { target := 627, numerator := 82641413450218791239680000 }, some { target := 628, numerator := 4958484807013127474380800 }, some { target := 629, numerator := 130573433251345690158694400 }, some { target := 630, numerator := 129747019116843502246297600 }, some { target := 631, numerator := 82641413450218791239680000 }, some { target := 632, numerator := 2002401447898801311737446400 }, some { target := 633, numerator := 128094190847839126421504000 }, some { target := 634, numerator := 74377272105196912115712000 }, some { target := 635, numerator := 130573433251345690158694400 }, some { target := 636, numerator := 4958484807013127474380800 }, some { target := 637, numerator := 128094190847839126421504000 }, some { target := 638, numerator := 4958484807013127474380800 }, some { target := 639, numerator := 130573433251345690158694400 }, some { target := 640, numerator := 130573433251345690158694400 }, some { target := 641, numerator := 4958484807013127474380800 }]

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

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 399, #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0], #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 80, numerator := 2990238546854918057443196928 }, some { target := 82, numerator := 116635403416137958520172576768 }, some { target := 85, numerator := 116635360634679687073901838336 }, some { target := 92, numerator := 2990252807341008539533443072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 115, numerator := 3376075778707165548726190080 }, some { target := 117, numerator := 131685132889188017684065812480 }, some { target := 120, numerator := 131685084587541582180211752960 }, some { target := 127, numerator := 3376091879255977383344209920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 176, numerator := 2893779238891856184622448640 }, some { target := 178, numerator := 112872971047875443729199267840 }, some { target := 181, numerator := 112872929646464213297324359680 }, some { target := 188, numerator := 2893793039362266328580751360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 211, numerator := 38101426645409439764195573760 }, some { target := 213, numerator := 1486160785463693342434457026560 }, some { target := 216, numerator := 1486160240345112141748104069120 }, some { target := 223, numerator := 38101608351603173326313226240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 237, numerator := 3376075778707165548726190080 }, some { target := 239, numerator := 131685132889188017684065812480 }, some { target := 242, numerator := 131685084587541582180211752960 }, some { target := 249, numerator := 3376091879255977383344209920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 286, numerator := 2893779238891856184622448640 }, some { target := 288, numerator := 112872971047875443729199267840 }, some { target := 291, numerator := 112872929646464213297324359680 }, some { target := 298, numerator := 2893793039362266328580751360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 3376075778707165548726190080 }, some { target := 314, numerator := 131685132889188017684065812480 }, some { target := 317, numerator := 131685084587541582180211752960 }, some { target := 324, numerator := 3376091879255977383344209920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 3376075778707165548726190080 }, some { target := 394, numerator := 131685132889188017684065812480 }, some { target := 397, numerator := 131685084587541582180211752960 }, some { target := 404, numerator := 3376091879255977383344209920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 427, numerator := 139962455854402777462905765888 }, some { target := 429, numerator := 5459289366348908961702271254528 }, some { target := 432, numerator := 5459287363900652449813921529856 }, some { target := 439, numerator := 139963123337154948092355674112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 453, numerator := 3472535086670227421546938368 }, some { target := 455, numerator := 135447565257450532475039121408 }, some { target := 458, numerator := 135447515575757055956789231616 }, some { target := 465, numerator := 3472551647234719594296901632 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 502, numerator := 38101426645409439764195573760 }, some { target := 504, numerator := 1486160785463693342434457026560 }, some { target := 507, numerator := 1486160240345112141748104069120 }, some { target := 514, numerator := 38101608351603173326313226240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 528, numerator := 139962455854402777462905765888 }, some { target := 530, numerator := 5459289366348908961702271254528 }, some { target := 533, numerator := 5459287363900652449813921529856 }, some { target := 540, numerator := 139963123337154948092355674112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 2990238546854918057443196928 }, some { target := 575, numerator := 116635403416137958520172576768 }, some { target := 578, numerator := 116635360634679687073901838336 }, some { target := 585, numerator := 2990252807341008539533443072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 642, numerator := 3376075778707165548726190080 }, some { target := 644, numerator := 131685132889188017684065812480 }, some { target := 647, numerator := 131685084587541582180211752960 }, some { target := 654, numerator := 3376091879255977383344209920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 668, numerator := 3472535086670227421546938368 }, some { target := 670, numerator := 135447565257450532475039121408 }, some { target := 673, numerator := 135447515575757055956789231616 }, some { target := 680, numerator := 3472551647234719594296901632 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 713, numerator := 3376075778707165548726190080 }, some { target := 715, numerator := 131685132889188017684065812480 }, some { target := 718, numerator := 131685084587541582180211752960 }, some { target := 725, numerator := 3376091879255977383344209920 }]

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

end Slot1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent2
