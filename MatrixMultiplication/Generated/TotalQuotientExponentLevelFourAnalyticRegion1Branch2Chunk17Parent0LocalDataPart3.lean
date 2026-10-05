import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk17Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 2,
parent 70; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 341, #[49931561730048, 0, 0, 181611853250560, 0, 49931561730048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 14, numerator := 52652850344674284322066268160 }, some { target := 15, numerator := 40952216934746665583829319680 }, some { target := 16, numerator := 46802533639710474952947793920 }, some { target := 17, numerator := 54992977026659808069713657856 }, some { target := 18, numerator := 649385154250982839972150640640 }, some { target := 19, numerator := 1460239049558966818531971170304 }, some { target := 20, numerator := 40952216934746665583829319680 }, some { target := 21, numerator := 649385154250982839972150640640 }, some { target := 22, numerator := 46802533639710474952947793920 }, some { target := 23, numerator := 45632470298717713079124099072 }, some { target := 24, numerator := 45632470298717713079124099072 }, some { target := 25, numerator := 45632470298717713079124099072 }, some { target := 26, numerator := 1460239049558966818531971170304 }, some { target := 27, numerator := 45632470298717713079124099072 }, some { target := 28, numerator := 52652850344674284322066268160 }, some { target := 29, numerator := 54992977026659808069713657856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 191509766542435186329727795200 }, some { target := 137, numerator := 148952040644116256034232729600 }, some { target := 138, numerator := 170230903593275721181980262400 }, some { target := 139, numerator := 200021311722098972388826808320 }, some { target := 140, numerator := 2361953787356700631399976140800 }, some { target := 141, numerator := 5311204192110202500877784186880 }, some { target := 142, numerator := 148952040644116256034232729600 }, some { target := 143, numerator := 2361953787356700631399976140800 }, some { target := 144, numerator := 170230903593275721181980262400 }, some { target := 145, numerator := 165975131003443828152430755840 }, some { target := 146, numerator := 165975131003443828152430755840 }, some { target := 147, numerator := 165975131003443828152430755840 }, some { target := 148, numerator := 5311204192110202500877784186880 }, some { target := 149, numerator := 165975131003443828152430755840 }, some { target := 150, numerator := 191509766542435186329727795200 }, some { target := 151, numerator := 200021311722098972388826808320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 52652850344674284322066268160 }, some { target := 268, numerator := 40952216934746665583829319680 }, some { target := 269, numerator := 46802533639710474952947793920 }, some { target := 270, numerator := 54992977026659808069713657856 }, some { target := 271, numerator := 649385154250982839972150640640 }, some { target := 272, numerator := 1460239049558966818531971170304 }, some { target := 273, numerator := 40952216934746665583829319680 }, some { target := 274, numerator := 649385154250982839972150640640 }, some { target := 275, numerator := 46802533639710474952947793920 }, some { target := 276, numerator := 45632470298717713079124099072 }, some { target := 277, numerator := 45632470298717713079124099072 }, some { target := 278, numerator := 45632470298717713079124099072 }, some { target := 279, numerator := 1460239049558966818531971170304 }, some { target := 280, numerator := 45632470298717713079124099072 }, some { target := 281, numerator := 52652850344674284322066268160 }, some { target := 282, numerator := 54992977026659808069713657856 }]

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

end Slot13

namespace Slot14

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨14, 540, #[2199023255552, 2611340115968, 1992864825344, 20547123544064, 2473901162496, 1992864825344, 2473901162496, 2473901162496, 105965433126912, 2473901162496, 20547123544064, 105965433126912, 2199023255552, 2473901162496, 2473901162496, 2611340115968, 0, 0, 0], #[153243090944, 22633202581504, 0, 235902085365760, 0, 0, 0, 0, 0, 0, 0, 22633202581504, 0, 0, 0, 0, 0, 0, 153243090944]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 56, numerator := 181971965198804088017387520 }, some { target := 57, numerator := 26876306965147302618275512320 }, some { target := 59, numerator := 280127252746360460810177740800 }, some { target := 67, numerator := 26876306965147302618275512320 }, some { target := 74, numerator := 181971965198804088017387520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 91, numerator := 216091708673579854520647680 }, some { target := 92, numerator := 31915614521112421859202170880 }, some { target := 94, numerator := 332651112636303047212086067200 }, some { target := 102, numerator := 31915614521112421859202170880 }, some { target := 109, numerator := 216091708673579854520647680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 164912093461416204765757440 }, some { target := 153, numerator := 24356653187164742997812183040 }, some { target := 155, numerator := 253865322801389167609223577600 }, some { target := 163, numerator := 24356653187164742997812183040 }, some { target := 170, numerator := 164912093461416204765757440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 187, numerator := 1700300549826325697412464640 }, some { target := 188, numerator := 251125493205595108839511818240 }, some { target := 190, numerator := 2617439017848805555695098265600 }, some { target := 198, numerator := 251125493205595108839511818240 }, some { target := 205, numerator := 1700300549826325697412464640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 222, numerator := 204718460848654599019560960 }, some { target := 223, numerator := 30235845335790715445559951360 }, some { target := 225, numerator := 315143159339655518411449958400 }, some { target := 233, numerator := 30235845335790715445559951360 }, some { target := 240, numerator := 204718460848654599019560960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 164912093461416204765757440 }, some { target := 284, numerator := 24356653187164742997812183040 }, some { target := 286, numerator := 253865322801389167609223577600 }, some { target := 294, numerator := 24356653187164742997812183040 }, some { target := 301, numerator := 164912093461416204765757440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 318, numerator := 204718460848654599019560960 }, some { target := 319, numerator := 30235845335790715445559951360 }, some { target := 321, numerator := 315143159339655518411449958400 }, some { target := 329, numerator := 30235845335790715445559951360 }, some { target := 336, numerator := 204718460848654599019560960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 419, numerator := 204718460848654599019560960 }, some { target := 420, numerator := 30235845335790715445559951360 }, some { target := 422, numerator := 315143159339655518411449958400 }, some { target := 430, numerator := 30235845335790715445559951360 }, some { target := 437, numerator := 204718460848654599019560960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 454, numerator := 8768774073017371991337861120 }, some { target := 455, numerator := 1295102041883035644918151249920 }, some { target := 457, numerator := 13498631991715244705290439884800 }, some { target := 465, numerator := 1295102041883035644918151249920 }, some { target := 472, numerator := 8768774073017371991337861120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 489, numerator := 204718460848654599019560960 }, some { target := 490, numerator := 30235845335790715445559951360 }, some { target := 492, numerator := 315143159339655518411449958400 }, some { target := 500, numerator := 30235845335790715445559951360 }, some { target := 507, numerator := 204718460848654599019560960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 550, numerator := 1700300549826325697412464640 }, some { target := 551, numerator := 251125493205595108839511818240 }, some { target := 553, numerator := 2617439017848805555695098265600 }, some { target := 561, numerator := 251125493205595108839511818240 }, some { target := 568, numerator := 1700300549826325697412464640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 585, numerator := 8768774073017371991337861120 }, some { target := 586, numerator := 1295102041883035644918151249920 }, some { target := 588, numerator := 13498631991715244705290439884800 }, some { target := 596, numerator := 1295102041883035644918151249920 }, some { target := 603, numerator := 8768774073017371991337861120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 181971965198804088017387520 }, some { target := 661, numerator := 26876306965147302618275512320 }, some { target := 663, numerator := 280127252746360460810177740800 }, some { target := 671, numerator := 26876306965147302618275512320 }, some { target := 678, numerator := 181971965198804088017387520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 766, numerator := 204718460848654599019560960 }, some { target := 767, numerator := 30235845335790715445559951360 }, some { target := 769, numerator := 315143159339655518411449958400 }, some { target := 777, numerator := 30235845335790715445559951360 }, some { target := 784, numerator := 204718460848654599019560960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 801, numerator := 204718460848654599019560960 }, some { target := 802, numerator := 30235845335790715445559951360 }, some { target := 804, numerator := 315143159339655518411449958400 }, some { target := 812, numerator := 30235845335790715445559951360 }, some { target := 819, numerator := 204718460848654599019560960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 876, numerator := 216091708673579854520647680 }, some { target := 877, numerator := 31915614521112421859202170880 }, some { target := 879, numerator := 332651112636303047212086067200 }, some { target := 887, numerator := 31915614521112421859202170880 }, some { target := 894, numerator := 216091708673579854520647680 }]

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

end Slot14

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 124, #[50466754920448, 0, 0, 180541483646976, 0, 50466738143232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 14, numerator := 10350520909866128083834109952 }, some { target := 15, numerator := 870367456375653935343787311104 }, some { target := 20, numerator := 870367246396125201727896944640 }, some { target := 28, numerator := 10350730889394861699724476416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 37028305159147927064568397824 }, some { target := 137, numerator := 3113682108940922814797916930048 }, some { target := 142, numerator := 3113681357753022724563460423680 }, some { target := 150, numerator := 37029056347048017299024904192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 10350517468929113388239290368 }, some { target := 268, numerator := 870367167029869012121378881536 }, some { target := 273, numerator := 870366957050410084299712757760 }, some { target := 281, numerator := 10350727448388041209905414144 }]

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

end Slot15

namespace Slot16

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨16, 7, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 50989851738112, 38139309588480, 44255343017984, 2130303778816, 44186623541248, 44392781971456, 2130303778816, 50989851738112, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 4, numerator := 2098695222850996247289921536 }, some { target := 5, numerator := 50233285656627071467391025152 }, some { target := 6, numerator := 37573414473622674749867950080 }, some { target := 7, numerator := 43598700758581986556603531264 }, some { target := 8, numerator := 2098695222850996247289921536 }, some { target := 9, numerator := 43531000912683567322819985408 }, some { target := 10, numerator := 43734100450378825024170622976 }, some { target := 11, numerator := 2098695222850996247289921536 }, some { target := 12, numerator := 50233285656627071467391025152 }, some { target := 13, numerator := 2098695222850996247289921536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 2098695222850996247289921536 }, some { target := 127, numerator := 50233285656627071467391025152 }, some { target := 128, numerator := 37573414473622674749867950080 }, some { target := 129, numerator := 43598700758581986556603531264 }, some { target := 130, numerator := 2098695222850996247289921536 }, some { target := 131, numerator := 43531000912683567322819985408 }, some { target := 132, numerator := 43734100450378825024170622976 }, some { target := 133, numerator := 2098695222850996247289921536 }, some { target := 134, numerator := 50233285656627071467391025152 }, some { target := 135, numerator := 2098695222850996247289921536 }]

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

end Slot16

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent0
