import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 34; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 23, #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0], #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0]⟩

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
  [some { target := 29, numerator := 161618270509730737793531904 }, some { target := 30, numerator := 121213702882298053345148928 }, some { target := 31, numerator := 127947797486870167419879424 }, some { target := 32, numerator := 164985317812016794830897152 }, some { target := 33, numerator := 2208783030299653416511602688 }, some { target := 34, numerator := 3862003255722107421857939456 }, some { target := 35, numerator := 117846655580011996307783680 }, some { target := 36, numerator := 2208783030299653416511602688 }, some { target := 37, numerator := 124580750184584110382514176 }, some { target := 38, numerator := 127947797486870167419879424 }, some { target := 39, numerator := 127947797486870167419879424 }, some { target := 40, numerator := 124580750184584110382514176 }, some { target := 41, numerator := 3862003255722107421857939456 }, some { target := 42, numerator := 124580750184584110382514176 }, some { target := 43, numerator := 161618270509730737793531904 }, some { target := 44, numerator := 164985317812016794830897152 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 182472240898083091057213440 }, some { target := 56, numerator := 136854180673562318292910080 }, some { target := 57, numerator := 144457190710982447086960640 }, some { target := 58, numerator := 186273745916793155454238720 }, some { target := 59, numerator := 2493787292273802244448583680 }, some { target := 60, numerator := 4360326256460443863387996160 }, some { target := 61, numerator := 133052675654852253895884800 }, some { target := 62, numerator := 2493787292273802244448583680 }, some { target := 63, numerator := 140655685692272382689935360 }, some { target := 64, numerator := 144457190710982447086960640 }, some { target := 65, numerator := 144457190710982447086960640 }, some { target := 66, numerator := 140655685692272382689935360 }, some { target := 67, numerator := 4360326256460443863387996160 }, some { target := 68, numerator := 140655685692272382689935360 }, some { target := 69, numerator := 182472240898083091057213440 }, some { target := 70, numerator := 186273745916793155454238720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 156404777912642649477611520 }, some { target := 105, numerator := 117303583434481987108208640 }, some { target := 106, numerator := 123820449180842097503109120 }, some { target := 107, numerator := 159663210785822704675061760 }, some { target := 108, numerator := 2137531964806116209527357440 }, some { target := 109, numerator := 3737422505537523311475425280 }, some { target := 110, numerator := 114045150561301931910758400 }, some { target := 111, numerator := 2137531964806116209527357440 }, some { target := 112, numerator := 120562016307662042305658880 }, some { target := 113, numerator := 123820449180842097503109120 }, some { target := 114, numerator := 123820449180842097503109120 }, some { target := 115, numerator := 120562016307662042305658880 }, some { target := 116, numerator := 3737422505537523311475425280 }, some { target := 117, numerator := 120562016307662042305658880 }, some { target := 118, numerator := 156404777912642649477611520 }, some { target := 119, numerator := 159663210785822704675061760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 130, numerator := 2059329575849794884788551680 }, some { target := 131, numerator := 1544497181887346163591413760 }, some { target := 132, numerator := 1630302580881087617124270080 }, some { target := 133, numerator := 2102232275346665611554979840 }, some { target := 134, numerator := 28144170869947196758776872960 }, some { target := 135, numerator := 49209396322910723601093099520 }, some { target := 136, numerator := 1501594482390475436824985600 }, some { target := 137, numerator := 28144170869947196758776872960 }, some { target := 138, numerator := 1587399881384216890357841920 }, some { target := 139, numerator := 1630302580881087617124270080 }, some { target := 140, numerator := 1630302580881087617124270080 }, some { target := 141, numerator := 1587399881384216890357841920 }, some { target := 142, numerator := 49209396322910723601093099520 }, some { target := 143, numerator := 1587399881384216890357841920 }, some { target := 144, numerator := 2059329575849794884788551680 }, some { target := 145, numerator := 2102232275346665611554979840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 165, numerator := 182472240898083091057213440 }, some { target := 166, numerator := 136854180673562318292910080 }, some { target := 167, numerator := 144457190710982447086960640 }, some { target := 168, numerator := 186273745916793155454238720 }, some { target := 169, numerator := 2493787292273802244448583680 }, some { target := 170, numerator := 4360326256460443863387996160 }, some { target := 171, numerator := 133052675654852253895884800 }, some { target := 172, numerator := 2493787292273802244448583680 }, some { target := 173, numerator := 140655685692272382689935360 }, some { target := 174, numerator := 144457190710982447086960640 }, some { target := 175, numerator := 144457190710982447086960640 }, some { target := 176, numerator := 140655685692272382689935360 }, some { target := 177, numerator := 4360326256460443863387996160 }, some { target := 178, numerator := 140655685692272382689935360 }, some { target := 179, numerator := 182472240898083091057213440 }, some { target := 180, numerator := 186273745916793155454238720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 156404777912642649477611520 }, some { target := 227, numerator := 117303583434481987108208640 }, some { target := 228, numerator := 123820449180842097503109120 }, some { target := 229, numerator := 159663210785822704675061760 }, some { target := 230, numerator := 2137531964806116209527357440 }, some { target := 231, numerator := 3737422505537523311475425280 }, some { target := 232, numerator := 114045150561301931910758400 }, some { target := 233, numerator := 2137531964806116209527357440 }, some { target := 234, numerator := 120562016307662042305658880 }, some { target := 235, numerator := 123820449180842097503109120 }, some { target := 236, numerator := 123820449180842097503109120 }, some { target := 237, numerator := 120562016307662042305658880 }, some { target := 238, numerator := 3737422505537523311475425280 }, some { target := 239, numerator := 120562016307662042305658880 }, some { target := 240, numerator := 156404777912642649477611520 }, some { target := 241, numerator := 159663210785822704675061760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 261, numerator := 182472240898083091057213440 }, some { target := 262, numerator := 136854180673562318292910080 }, some { target := 263, numerator := 144457190710982447086960640 }, some { target := 264, numerator := 186273745916793155454238720 }, some { target := 265, numerator := 2493787292273802244448583680 }, some { target := 266, numerator := 4360326256460443863387996160 }, some { target := 267, numerator := 133052675654852253895884800 }, some { target := 268, numerator := 2493787292273802244448583680 }, some { target := 269, numerator := 140655685692272382689935360 }, some { target := 270, numerator := 144457190710982447086960640 }, some { target := 271, numerator := 144457190710982447086960640 }, some { target := 272, numerator := 140655685692272382689935360 }, some { target := 273, numerator := 4360326256460443863387996160 }, some { target := 274, numerator := 140655685692272382689935360 }, some { target := 275, numerator := 182472240898083091057213440 }, some { target := 276, numerator := 186273745916793155454238720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 371, numerator := 182472240898083091057213440 }, some { target := 372, numerator := 136854180673562318292910080 }, some { target := 373, numerator := 144457190710982447086960640 }, some { target := 374, numerator := 186273745916793155454238720 }, some { target := 375, numerator := 2493787292273802244448583680 }, some { target := 376, numerator := 4360326256460443863387996160 }, some { target := 377, numerator := 133052675654852253895884800 }, some { target := 378, numerator := 2493787292273802244448583680 }, some { target := 379, numerator := 140655685692272382689935360 }, some { target := 380, numerator := 144457190710982447086960640 }, some { target := 381, numerator := 144457190710982447086960640 }, some { target := 382, numerator := 140655685692272382689935360 }, some { target := 383, numerator := 4360326256460443863387996160 }, some { target := 384, numerator := 140655685692272382689935360 }, some { target := 385, numerator := 182472240898083091057213440 }, some { target := 386, numerator := 186273745916793155454238720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 397, numerator := 7564777758374816146400477184 }, some { target := 398, numerator := 5673583318781112109800357888 }, some { target := 399, numerator := 5988782392046729449233711104 }, some { target := 400, numerator := 7722377295007624816117153792 }, some { target := 401, numerator := 103385296031122487334139854848 }, some { target := 402, numerator := 180766668517831544165028069376 }, some { target := 403, numerator := 5515983782148303440083681280 }, some { target := 404, numerator := 103385296031122487334139854848 }, some { target := 405, numerator := 5831182855413920779517034496 }, some { target := 406, numerator := 5988782392046729449233711104 }, some { target := 407, numerator := 5988782392046729449233711104 }, some { target := 408, numerator := 5831182855413920779517034496 }, some { target := 409, numerator := 180766668517831544165028069376 }, some { target := 410, numerator := 5831182855413920779517034496 }, some { target := 411, numerator := 7564777758374816146400477184 }, some { target := 412, numerator := 7722377295007624816117153792 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 432, numerator := 187685733495171179373133824 }, some { target := 433, numerator := 140764300121378384529850368 }, some { target := 434, numerator := 148584539017010517003730944 }, some { target := 435, numerator := 191595852942987245610074112 }, some { target := 436, numerator := 2565038357767339451432828928 }, some { target := 437, numerator := 4484907006645027973770510336 }, some { target := 438, numerator := 136854180673562318292910080 }, some { target := 439, numerator := 2565038357767339451432828928 }, some { target := 440, numerator := 144674419569194450766790656 }, some { target := 441, numerator := 148584539017010517003730944 }, some { target := 442, numerator := 148584539017010517003730944 }, some { target := 443, numerator := 144674419569194450766790656 }, some { target := 444, numerator := 4484907006645027973770510336 }, some { target := 445, numerator := 144674419569194450766790656 }, some { target := 446, numerator := 187685733495171179373133824 }, some { target := 447, numerator := 191595852942987245610074112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 493, numerator := 2059329575849794884788551680 }, some { target := 494, numerator := 1544497181887346163591413760 }, some { target := 495, numerator := 1630302580881087617124270080 }, some { target := 496, numerator := 2102232275346665611554979840 }, some { target := 497, numerator := 28144170869947196758776872960 }, some { target := 498, numerator := 49209396322910723601093099520 }, some { target := 499, numerator := 1501594482390475436824985600 }, some { target := 500, numerator := 28144170869947196758776872960 }, some { target := 501, numerator := 1587399881384216890357841920 }, some { target := 502, numerator := 1630302580881087617124270080 }, some { target := 503, numerator := 1630302580881087617124270080 }, some { target := 504, numerator := 1587399881384216890357841920 }, some { target := 505, numerator := 49209396322910723601093099520 }, some { target := 506, numerator := 1587399881384216890357841920 }, some { target := 507, numerator := 2059329575849794884788551680 }, some { target := 508, numerator := 2102232275346665611554979840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 528, numerator := 7564777758374816146400477184 }, some { target := 529, numerator := 5673583318781112109800357888 }, some { target := 530, numerator := 5988782392046729449233711104 }, some { target := 531, numerator := 7722377295007624816117153792 }, some { target := 532, numerator := 103385296031122487334139854848 }, some { target := 533, numerator := 180766668517831544165028069376 }, some { target := 534, numerator := 5515983782148303440083681280 }, some { target := 535, numerator := 103385296031122487334139854848 }, some { target := 536, numerator := 5831182855413920779517034496 }, some { target := 537, numerator := 5988782392046729449233711104 }, some { target := 538, numerator := 5988782392046729449233711104 }, some { target := 539, numerator := 5831182855413920779517034496 }, some { target := 540, numerator := 180766668517831544165028069376 }, some { target := 541, numerator := 5831182855413920779517034496 }, some { target := 542, numerator := 7564777758374816146400477184 }, some { target := 543, numerator := 7722377295007624816117153792 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 161618270509730737793531904 }, some { target := 625, numerator := 121213702882298053345148928 }, some { target := 626, numerator := 127947797486870167419879424 }, some { target := 627, numerator := 164985317812016794830897152 }, some { target := 628, numerator := 2208783030299653416511602688 }, some { target := 629, numerator := 3862003255722107421857939456 }, some { target := 630, numerator := 117846655580011996307783680 }, some { target := 631, numerator := 2208783030299653416511602688 }, some { target := 632, numerator := 124580750184584110382514176 }, some { target := 633, numerator := 127947797486870167419879424 }, some { target := 634, numerator := 127947797486870167419879424 }, some { target := 635, numerator := 124580750184584110382514176 }, some { target := 636, numerator := 3862003255722107421857939456 }, some { target := 637, numerator := 124580750184584110382514176 }, some { target := 638, numerator := 161618270509730737793531904 }, some { target := 639, numerator := 164985317812016794830897152 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 760, numerator := 182472240898083091057213440 }, some { target := 761, numerator := 136854180673562318292910080 }, some { target := 762, numerator := 144457190710982447086960640 }, some { target := 763, numerator := 186273745916793155454238720 }, some { target := 764, numerator := 2493787292273802244448583680 }, some { target := 765, numerator := 4360326256460443863387996160 }, some { target := 766, numerator := 133052675654852253895884800 }, some { target := 767, numerator := 2493787292273802244448583680 }, some { target := 768, numerator := 140655685692272382689935360 }, some { target := 769, numerator := 144457190710982447086960640 }, some { target := 770, numerator := 144457190710982447086960640 }, some { target := 771, numerator := 140655685692272382689935360 }, some { target := 772, numerator := 4360326256460443863387996160 }, some { target := 773, numerator := 140655685692272382689935360 }, some { target := 774, numerator := 182472240898083091057213440 }, some { target := 775, numerator := 186273745916793155454238720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 795, numerator := 187685733495171179373133824 }, some { target := 796, numerator := 140764300121378384529850368 }, some { target := 797, numerator := 148584539017010517003730944 }, some { target := 798, numerator := 191595852942987245610074112 }, some { target := 799, numerator := 2565038357767339451432828928 }, some { target := 800, numerator := 4484907006645027973770510336 }, some { target := 801, numerator := 136854180673562318292910080 }, some { target := 802, numerator := 2565038357767339451432828928 }, some { target := 803, numerator := 144674419569194450766790656 }, some { target := 804, numerator := 148584539017010517003730944 }, some { target := 805, numerator := 148584539017010517003730944 }, some { target := 806, numerator := 144674419569194450766790656 }, some { target := 807, numerator := 4484907006645027973770510336 }, some { target := 808, numerator := 144674419569194450766790656 }, some { target := 809, numerator := 187685733495171179373133824 }, some { target := 810, numerator := 191595852942987245610074112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 891, numerator := 182472240898083091057213440 }, some { target := 892, numerator := 136854180673562318292910080 }, some { target := 893, numerator := 144457190710982447086960640 }, some { target := 894, numerator := 186273745916793155454238720 }, some { target := 895, numerator := 2493787292273802244448583680 }, some { target := 896, numerator := 4360326256460443863387996160 }, some { target := 897, numerator := 133052675654852253895884800 }, some { target := 898, numerator := 2493787292273802244448583680 }, some { target := 899, numerator := 140655685692272382689935360 }, some { target := 900, numerator := 144457190710982447086960640 }, some { target := 901, numerator := 144457190710982447086960640 }, some { target := 902, numerator := 140655685692272382689935360 }, some { target := 903, numerator := 4360326256460443863387996160 }, some { target := 904, numerator := 140655685692272382689935360 }, some { target := 905, numerator := 182472240898083091057213440 }, some { target := 906, numerator := 186273745916793155454238720 }]

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

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 766, #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416], #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576]⟩

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
  [some { target := 71, numerator := 65366332773094975504121856 }, some { target := 72, numerator := 7725880866662800397546029056 }, some { target := 74, numerator := 73317069373482345072024354816 }, some { target := 82, numerator := 7725886165490035570614730752 }, some { target := 89, numerator := 65366332773094975504121856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 947811825209877144809766912 }, some { target := 147, numerator := 112025272566610605764417421312 }, some { target := 149, numerator := 1063097505915494003544353144832 }, some { target := 157, numerator := 112025349399605515773913595904 }, some { target := 164, numerator := 947811825209877144809766912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 181, numerator := 1677735874509437704605794304 }, some { target := 182, numerator := 198297608911011876870348079104 }, some { target := 184, numerator := 1881804780586046856848625106944 }, some { target := 192, numerator := 198297744914244246312444755968 }, some { target := 199, numerator := 1677735874509437704605794304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 54471943977579146253434880 }, some { target := 243, numerator := 6438234055552333664621690880 }, some { target := 245, numerator := 61097557811235287560020295680 }, some { target := 253, numerator := 6438238471241696308845608960 }, some { target := 260, numerator := 54471943977579146253434880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 277, numerator := 1045861324369519608065949696 }, some { target := 278, numerator := 123614093866604806360736464896 }, some { target := 280, numerator := 1173073109975717521152389677056 }, some { target := 288, numerator := 123614178647840569129835692032 }, some { target := 295, numerator := 1045861324369519608065949696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 54471943977579146253434880 }, some { target := 313, numerator := 6438234055552333664621690880 }, some { target := 315, numerator := 61097557811235287560020295680 }, some { target := 323, numerator := 6438238471241696308845608960 }, some { target := 330, numerator := 54471943977579146253434880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 413, numerator := 1666841485713921875355107328 }, some { target := 414, numerator := 197009962099901410137423740928 }, some { target := 416, numerator := 1869585269023799799336621047808 }, some { target := 424, numerator := 197010097219995907050675634176 }, some { target := 431, numerator := 1666841485713921875355107328 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 448, numerator := 1743102207282532680109916160 }, some { target := 449, numerator := 206023489777674677267894108160 }, some { target := 451, numerator := 1955121849959529201920649461760 }, some { target := 459, numerator := 206023631079734281883059486720 }, some { target := 466, numerator := 1743102207282532680109916160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 509, numerator := 1045861324369519608065949696 }, some { target := 510, numerator := 123614093866604806360736464896 }, some { target := 512, numerator := 1173073109975717521152389677056 }, some { target := 520, numerator := 123614178647840569129835692032 }, some { target := 527, numerator := 1045861324369519608065949696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 26702146937809297493433778176 }, some { target := 545, numerator := 3156022334031753962397552869376 }, some { target := 547, numerator := 29950022839067537961921948942336 }, some { target := 555, numerator := 3156024498602679530596117512192 }, some { target := 562, numerator := 26702146937809297493433778176 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 579, numerator := 1710419040895985192357855232 }, some { target := 580, numerator := 202160549344343277069121093632 }, some { target := 582, numerator := 1918463315272788029384637284352 }, some { target := 590, numerator := 202160687996989264097752121344 }, some { target := 597, numerator := 1710419040895985192357855232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 947811825209877144809766912 }, some { target := 641, numerator := 112025272566610605764417421312 }, some { target := 643, numerator := 1063097505915494003544353144832 }, some { target := 651, numerator := 112025349399605515773913595904 }, some { target := 658, numerator := 947811825209877144809766912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 675, numerator := 1666841485713921875355107328 }, some { target := 676, numerator := 197009962099901410137423740928 }, some { target := 678, numerator := 1869585269023799799336621047808 }, some { target := 686, numerator := 197010097219995907050675634176 }, some { target := 693, numerator := 1666841485713921875355107328 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 776, numerator := 54471943977579146253434880 }, some { target := 777, numerator := 6438234055552333664621690880 }, some { target := 779, numerator := 61097557811235287560020295680 }, some { target := 787, numerator := 6438238471241696308845608960 }, some { target := 794, numerator := 54471943977579146253434880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 811, numerator := 1710419040895985192357855232 }, some { target := 812, numerator := 202160549344343277069121093632 }, some { target := 814, numerator := 1918463315272788029384637284352 }, some { target := 822, numerator := 202160687996989264097752121344 }, some { target := 829, numerator := 1710419040895985192357855232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 54471943977579146253434880 }, some { target := 847, numerator := 6438234055552333664621690880 }, some { target := 849, numerator := 61097557811235287560020295680 }, some { target := 857, numerator := 6438238471241696308845608960 }, some { target := 864, numerator := 54471943977579146253434880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 907, numerator := 1666841485713921875355107328 }, some { target := 908, numerator := 197009962099901410137423740928 }, some { target := 910, numerator := 1869585269023799799336621047808 }, some { target := 918, numerator := 197010097219995907050675634176 }, some { target := 925, numerator := 1666841485713921875355107328 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 942, numerator := 1743102207282532680109916160 }, some { target := 943, numerator := 206023489777674677267894108160 }, some { target := 945, numerator := 1955121849959529201920649461760 }, some { target := 953, numerator := 206023631079734281883059486720 }, some { target := 960, numerator := 1743102207282532680109916160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 65366332773094975504121856 }, some { target := 1018, numerator := 7725880866662800397546029056 }, some { target := 1020, numerator := 73317069373482345072024354816 }, some { target := 1028, numerator := 7725886165490035570614730752 }, some { target := 1035, numerator := 65366332773094975504121856 }]

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

end Slot1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent0
