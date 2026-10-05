import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk9Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 41; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 62, #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0], #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 121, numerator := 51237676339135650568601600 }, some { target := 122, numerator := 860792962497478929552506880 }, some { target := 123, numerator := 1865051418744537680697098240 }, some { target := 124, numerator := 61485211606962780682321920 }, some { target := 125, numerator := 983763385711404490917150720 }, some { target := 126, numerator := 71732746874789910796042240 }, some { target := 127, numerator := 1865051418744537680697098240 }, some { target := 128, numerator := 1865051418744537680697098240 }, some { target := 129, numerator := 983763385711404490917150720 }, some { target := 130, numerator := 23015964211539734235415838720 }, some { target := 131, numerator := 1844556348208883420469657600 }, some { target := 132, numerator := 860792962497478929552506880 }, some { target := 133, numerator := 1865051418744537680697098240 }, some { target := 134, numerator := 71732746874789910796042240 }, some { target := 135, numerator := 1844556348208883420469657600 }, some { target := 136, numerator := 71732746874789910796042240 }, some { target := 137, numerator := 1865051418744537680697098240 }, some { target := 138, numerator := 1865051418744537680697098240 }, some { target := 139, numerator := 61485211606962780682321920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 52701609948825240584847360 }, some { target := 197, numerator := 885387047140264041825435648 }, some { target := 198, numerator := 1918338602137238757288443904 }, some { target := 199, numerator := 63241931938590288701816832 }, some { target := 200, numerator := 1011870911017444619229069312 }, some { target := 201, numerator := 73782253928355336818786304 }, some { target := 202, numerator := 1918338602137238757288443904 }, some { target := 203, numerator := 1918338602137238757288443904 }, some { target := 204, numerator := 1011870911017444619229069312 }, some { target := 205, numerator := 23673563189012298070713434112 }, some { target := 206, numerator := 1897257958157708661054504960 }, some { target := 207, numerator := 885387047140264041825435648 }, some { target := 208, numerator := 1918338602137238757288443904 }, some { target := 209, numerator := 73782253928355336818786304 }, some { target := 210, numerator := 1897257958157708661054504960 }, some { target := 211, numerator := 73782253928355336818786304 }, some { target := 212, numerator := 1918338602137238757288443904 }, some { target := 213, numerator := 1918338602137238757288443904 }, some { target := 214, numerator := 63241931938590288701816832 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 231, numerator := 51237676339135650568601600 }, some { target := 232, numerator := 860792962497478929552506880 }, some { target := 233, numerator := 1865051418744537680697098240 }, some { target := 234, numerator := 61485211606962780682321920 }, some { target := 235, numerator := 983763385711404490917150720 }, some { target := 236, numerator := 71732746874789910796042240 }, some { target := 237, numerator := 1865051418744537680697098240 }, some { target := 238, numerator := 1865051418744537680697098240 }, some { target := 239, numerator := 983763385711404490917150720 }, some { target := 240, numerator := 23015964211539734235415838720 }, some { target := 241, numerator := 1844556348208883420469657600 }, some { target := 242, numerator := 860792962497478929552506880 }, some { target := 243, numerator := 1865051418744537680697098240 }, some { target := 244, numerator := 71732746874789910796042240 }, some { target := 245, numerator := 1844556348208883420469657600 }, some { target := 246, numerator := 71732746874789910796042240 }, some { target := 247, numerator := 1865051418744537680697098240 }, some { target := 248, numerator := 1865051418744537680697098240 }, some { target := 249, numerator := 61485211606962780682321920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 45381941900377290503618560 }, some { target := 338, numerator := 762416623926338480460791808 }, some { target := 339, numerator := 1651902685173733374331715584 }, some { target := 340, numerator := 54458330280452748604342272 }, some { target := 341, numerator := 871333284487243977669476352 }, some { target := 342, numerator := 63534718660528206705065984 }, some { target := 343, numerator := 1651902685173733374331715584 }, some { target := 344, numerator := 1651902685173733374331715584 }, some { target := 345, numerator := 871333284487243977669476352 }, some { target := 346, numerator := 20385568301649478894225457152 }, some { target := 347, numerator := 1633749908413582458130268160 }, some { target := 348, numerator := 762416623926338480460791808 }, some { target := 349, numerator := 1651902685173733374331715584 }, some { target := 350, numerator := 63534718660528206705065984 }, some { target := 351, numerator := 1633749908413582458130268160 }, some { target := 352, numerator := 63534718660528206705065984 }, some { target := 353, numerator := 1651902685173733374331715584 }, some { target := 354, numerator := 1651902685173733374331715584 }, some { target := 355, numerator := 54458330280452748604342272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 412, numerator := 2124167667659595113572597760 }, some { target := 413, numerator := 35686016816681197908019642368 }, some { target := 414, numerator := 77319703102809262134042558464 }, some { target := 415, numerator := 2549001201191514136287117312 }, some { target := 416, numerator := 40784019219064226180593876992 }, some { target := 417, numerator := 2973834734723433159001636864 }, some { target := 418, numerator := 77319703102809262134042558464 }, some { target := 419, numerator := 77319703102809262134042558464 }, some { target := 420, numerator := 40784019219064226180593876992 }, some { target := 421, numerator := 954176116312690125016810913792 }, some { target := 422, numerator := 76470036035745424088613519360 }, some { target := 423, numerator := 35686016816681197908019642368 }, some { target := 424, numerator := 77319703102809262134042558464 }, some { target := 425, numerator := 2973834734723433159001636864 }, some { target := 426, numerator := 76470036035745424088613519360 }, some { target := 427, numerator := 2973834734723433159001636864 }, some { target := 428, numerator := 77319703102809262134042558464 }, some { target := 429, numerator := 77319703102809262134042558464 }, some { target := 430, numerator := 2549001201191514136287117312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 447, numerator := 578253775827388056417075200 }, some { target := 448, numerator := 9714663433900119347806863360 }, some { target := 449, numerator := 21048437440116925253581537280 }, some { target := 450, numerator := 693904530992865667700490240 }, some { target := 451, numerator := 11102472495885850683207843840 }, some { target := 452, numerator := 809555286158343278983905280 }, some { target := 453, numerator := 21048437440116925253581537280 }, some { target := 454, numerator := 21048437440116925253581537280 }, some { target := 455, numerator := 11102472495885850683207843840 }, some { target := 456, numerator := 259751596101662714942550179840 }, some { target := 457, numerator := 20817135929785970031014707200 }, some { target := 458, numerator := 9714663433900119347806863360 }, some { target := 459, numerator := 21048437440116925253581537280 }, some { target := 460, numerator := 809555286158343278983905280 }, some { target := 461, numerator := 20817135929785970031014707200 }, some { target := 462, numerator := 809555286158343278983905280 }, some { target := 463, numerator := 21048437440116925253581537280 }, some { target := 464, numerator := 21048437440116925253581537280 }, some { target := 465, numerator := 693904530992865667700490240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 52701609948825240584847360 }, some { target := 509, numerator := 885387047140264041825435648 }, some { target := 510, numerator := 1918338602137238757288443904 }, some { target := 511, numerator := 63241931938590288701816832 }, some { target := 512, numerator := 1011870911017444619229069312 }, some { target := 513, numerator := 73782253928355336818786304 }, some { target := 514, numerator := 1918338602137238757288443904 }, some { target := 515, numerator := 1918338602137238757288443904 }, some { target := 516, numerator := 1011870911017444619229069312 }, some { target := 517, numerator := 23673563189012298070713434112 }, some { target := 518, numerator := 1897257958157708661054504960 }, some { target := 519, numerator := 885387047140264041825435648 }, some { target := 520, numerator := 1918338602137238757288443904 }, some { target := 521, numerator := 73782253928355336818786304 }, some { target := 522, numerator := 1897257958157708661054504960 }, some { target := 523, numerator := 73782253928355336818786304 }, some { target := 524, numerator := 1918338602137238757288443904 }, some { target := 525, numerator := 1918338602137238757288443904 }, some { target := 526, numerator := 63241931938590288701816832 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 543, numerator := 2124167667659595113572597760 }, some { target := 544, numerator := 35686016816681197908019642368 }, some { target := 545, numerator := 77319703102809262134042558464 }, some { target := 546, numerator := 2549001201191514136287117312 }, some { target := 547, numerator := 40784019219064226180593876992 }, some { target := 548, numerator := 2973834734723433159001636864 }, some { target := 549, numerator := 77319703102809262134042558464 }, some { target := 550, numerator := 77319703102809262134042558464 }, some { target := 551, numerator := 40784019219064226180593876992 }, some { target := 552, numerator := 954176116312690125016810913792 }, some { target := 553, numerator := 76470036035745424088613519360 }, some { target := 554, numerator := 35686016816681197908019642368 }, some { target := 555, numerator := 77319703102809262134042558464 }, some { target := 556, numerator := 2973834734723433159001636864 }, some { target := 557, numerator := 76470036035745424088613519360 }, some { target := 558, numerator := 2973834734723433159001636864 }, some { target := 559, numerator := 77319703102809262134042558464 }, some { target := 560, numerator := 77319703102809262134042558464 }, some { target := 561, numerator := 2549001201191514136287117312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 578, numerator := 51237676339135650568601600 }, some { target := 579, numerator := 860792962497478929552506880 }, some { target := 580, numerator := 1865051418744537680697098240 }, some { target := 581, numerator := 61485211606962780682321920 }, some { target := 582, numerator := 983763385711404490917150720 }, some { target := 583, numerator := 71732746874789910796042240 }, some { target := 584, numerator := 1865051418744537680697098240 }, some { target := 585, numerator := 1865051418744537680697098240 }, some { target := 586, numerator := 983763385711404490917150720 }, some { target := 587, numerator := 23015964211539734235415838720 }, some { target := 588, numerator := 1844556348208883420469657600 }, some { target := 589, numerator := 860792962497478929552506880 }, some { target := 590, numerator := 1865051418744537680697098240 }, some { target := 591, numerator := 71732746874789910796042240 }, some { target := 592, numerator := 1844556348208883420469657600 }, some { target := 593, numerator := 71732746874789910796042240 }, some { target := 594, numerator := 1865051418744537680697098240 }, some { target := 595, numerator := 1865051418744537680697098240 }, some { target := 596, numerator := 61485211606962780682321920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 51237676339135650568601600 }, some { target := 680, numerator := 860792962497478929552506880 }, some { target := 681, numerator := 1865051418744537680697098240 }, some { target := 682, numerator := 61485211606962780682321920 }, some { target := 683, numerator := 983763385711404490917150720 }, some { target := 684, numerator := 71732746874789910796042240 }, some { target := 685, numerator := 1865051418744537680697098240 }, some { target := 686, numerator := 1865051418744537680697098240 }, some { target := 687, numerator := 983763385711404490917150720 }, some { target := 688, numerator := 23015964211539734235415838720 }, some { target := 689, numerator := 1844556348208883420469657600 }, some { target := 690, numerator := 860792962497478929552506880 }, some { target := 691, numerator := 1865051418744537680697098240 }, some { target := 692, numerator := 71732746874789910796042240 }, some { target := 693, numerator := 1844556348208883420469657600 }, some { target := 694, numerator := 71732746874789910796042240 }, some { target := 695, numerator := 1865051418744537680697098240 }, some { target := 696, numerator := 1865051418744537680697098240 }, some { target := 697, numerator := 61485211606962780682321920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 714, numerator := 43918008290687700487372800 }, some { target := 715, numerator := 737822539283553368187863040 }, some { target := 716, numerator := 1598615501781032297740369920 }, some { target := 717, numerator := 52701609948825240584847360 }, some { target := 718, numerator := 843225759181203849357557760 }, some { target := 719, numerator := 61485211606962780682321920 }, some { target := 720, numerator := 1598615501781032297740369920 }, some { target := 721, numerator := 1598615501781032297740369920 }, some { target := 722, numerator := 843225759181203849357557760 }, some { target := 723, numerator := 19727969324176915058927861760 }, some { target := 724, numerator := 1581048298464757217545420800 }, some { target := 725, numerator := 737822539283553368187863040 }, some { target := 726, numerator := 1598615501781032297740369920 }, some { target := 727, numerator := 61485211606962780682321920 }, some { target := 728, numerator := 1581048298464757217545420800 }, some { target := 729, numerator := 61485211606962780682321920 }, some { target := 730, numerator := 1598615501781032297740369920 }, some { target := 731, numerator := 1598615501781032297740369920 }, some { target := 732, numerator := 52701609948825240584847360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 775, numerator := 51237676339135650568601600 }, some { target := 776, numerator := 860792962497478929552506880 }, some { target := 777, numerator := 1865051418744537680697098240 }, some { target := 778, numerator := 61485211606962780682321920 }, some { target := 779, numerator := 983763385711404490917150720 }, some { target := 780, numerator := 71732746874789910796042240 }, some { target := 781, numerator := 1865051418744537680697098240 }, some { target := 782, numerator := 1865051418744537680697098240 }, some { target := 783, numerator := 983763385711404490917150720 }, some { target := 784, numerator := 23015964211539734235415838720 }, some { target := 785, numerator := 1844556348208883420469657600 }, some { target := 786, numerator := 860792962497478929552506880 }, some { target := 787, numerator := 1865051418744537680697098240 }, some { target := 788, numerator := 71732746874789910796042240 }, some { target := 789, numerator := 1844556348208883420469657600 }, some { target := 790, numerator := 71732746874789910796042240 }, some { target := 791, numerator := 1865051418744537680697098240 }, some { target := 792, numerator := 1865051418744537680697098240 }, some { target := 793, numerator := 61485211606962780682321920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 810, numerator := 578253775827388056417075200 }, some { target := 811, numerator := 9714663433900119347806863360 }, some { target := 812, numerator := 21048437440116925253581537280 }, some { target := 813, numerator := 693904530992865667700490240 }, some { target := 814, numerator := 11102472495885850683207843840 }, some { target := 815, numerator := 809555286158343278983905280 }, some { target := 816, numerator := 21048437440116925253581537280 }, some { target := 817, numerator := 21048437440116925253581537280 }, some { target := 818, numerator := 11102472495885850683207843840 }, some { target := 819, numerator := 259751596101662714942550179840 }, some { target := 820, numerator := 20817135929785970031014707200 }, some { target := 821, numerator := 9714663433900119347806863360 }, some { target := 822, numerator := 21048437440116925253581537280 }, some { target := 823, numerator := 809555286158343278983905280 }, some { target := 824, numerator := 20817135929785970031014707200 }, some { target := 825, numerator := 809555286158343278983905280 }, some { target := 826, numerator := 21048437440116925253581537280 }, some { target := 827, numerator := 21048437440116925253581537280 }, some { target := 828, numerator := 693904530992865667700490240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 845, numerator := 43918008290687700487372800 }, some { target := 846, numerator := 737822539283553368187863040 }, some { target := 847, numerator := 1598615501781032297740369920 }, some { target := 848, numerator := 52701609948825240584847360 }, some { target := 849, numerator := 843225759181203849357557760 }, some { target := 850, numerator := 61485211606962780682321920 }, some { target := 851, numerator := 1598615501781032297740369920 }, some { target := 852, numerator := 1598615501781032297740369920 }, some { target := 853, numerator := 843225759181203849357557760 }, some { target := 854, numerator := 19727969324176915058927861760 }, some { target := 855, numerator := 1581048298464757217545420800 }, some { target := 856, numerator := 737822539283553368187863040 }, some { target := 857, numerator := 1598615501781032297740369920 }, some { target := 858, numerator := 61485211606962780682321920 }, some { target := 859, numerator := 1581048298464757217545420800 }, some { target := 860, numerator := 61485211606962780682321920 }, some { target := 861, numerator := 1598615501781032297740369920 }, some { target := 862, numerator := 1598615501781032297740369920 }, some { target := 863, numerator := 52701609948825240584847360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 51237676339135650568601600 }, some { target := 907, numerator := 860792962497478929552506880 }, some { target := 908, numerator := 1865051418744537680697098240 }, some { target := 909, numerator := 61485211606962780682321920 }, some { target := 910, numerator := 983763385711404490917150720 }, some { target := 911, numerator := 71732746874789910796042240 }, some { target := 912, numerator := 1865051418744537680697098240 }, some { target := 913, numerator := 1865051418744537680697098240 }, some { target := 914, numerator := 983763385711404490917150720 }, some { target := 915, numerator := 23015964211539734235415838720 }, some { target := 916, numerator := 1844556348208883420469657600 }, some { target := 917, numerator := 860792962497478929552506880 }, some { target := 918, numerator := 1865051418744537680697098240 }, some { target := 919, numerator := 71732746874789910796042240 }, some { target := 920, numerator := 1844556348208883420469657600 }, some { target := 921, numerator := 71732746874789910796042240 }, some { target := 922, numerator := 1865051418744537680697098240 }, some { target := 923, numerator := 1865051418744537680697098240 }, some { target := 924, numerator := 61485211606962780682321920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 941, numerator := 45381941900377290503618560 }, some { target := 942, numerator := 762416623926338480460791808 }, some { target := 943, numerator := 1651902685173733374331715584 }, some { target := 944, numerator := 54458330280452748604342272 }, some { target := 945, numerator := 871333284487243977669476352 }, some { target := 946, numerator := 63534718660528206705065984 }, some { target := 947, numerator := 1651902685173733374331715584 }, some { target := 948, numerator := 1651902685173733374331715584 }, some { target := 949, numerator := 871333284487243977669476352 }, some { target := 950, numerator := 20385568301649478894225457152 }, some { target := 951, numerator := 1633749908413582458130268160 }, some { target := 952, numerator := 762416623926338480460791808 }, some { target := 953, numerator := 1651902685173733374331715584 }, some { target := 954, numerator := 63534718660528206705065984 }, some { target := 955, numerator := 1633749908413582458130268160 }, some { target := 956, numerator := 63534718660528206705065984 }, some { target := 957, numerator := 1651902685173733374331715584 }, some { target := 958, numerator := 1651902685173733374331715584 }, some { target := 959, numerator := 54458330280452748604342272 }]

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

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 12, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[51810056273920, 0, 0, 177854864162816, 0, 51810056273920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 613, numerator := 43749703149238226331956674560 }, some { target := 616, numerator := 150185081244316560116718501888 }, some { target := 618, numerator := 43749703149238226331956674560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 880, numerator := 43749703149238226331956674560 }, some { target := 883, numerator := 150185081244316560116718501888 }, some { target := 885, numerator := 43749703149238226331956674560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 976, numerator := 43749703149238226331956674560 }, some { target := 979, numerator := 150185081244316560116718501888 }, some { target := 981, numerator := 43749703149238226331956674560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1002, numerator := 43749703149238226331956674560 }, some { target := 1005, numerator := 150185081244316560116718501888 }, some { target := 1007, numerator := 43749703149238226331956674560 }]

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

end Slot4

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 100, #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3648641826816, 0, 137088846528512, 0, 0, 137078478209024, 0, 0, 0, 0, 0, 0, 3659010146304, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 250, numerator := 8788250473069785425274470400 }, some { target := 252, numerator := 330197146648437813467204812800 }, some { target := 255, numerator := 330172173139671985847638425600 }, some { target := 262, numerator := 8813223981835613044840857600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 562, numerator := 85123636376716325398826188800 }, some { target := 564, numerator := 3198313695093485356493412761600 }, some { target := 567, numerator := 3198071799862375667658339123200 }, some { target := 574, numerator := 85365531607826014233899827200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 925, numerator := 8788250473069785425274470400 }, some { target := 927, numerator := 330197146648437813467204812800 }, some { target := 930, numerator := 330172173139671985847638425600 }, some { target := 937, numerator := 8813223981835613044840857600 }]

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

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 542, #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0], #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 121, numerator := 132372745162728955067760640 }, some { target := 122, numerator := 21132937203211078505836052480 }, some { target := 124, numerator := 210874933558387482220486983680 }, some { target := 132, numerator := 21132937203211078505836052480 }, some { target := 139, numerator := 132357641015631427802234880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 11083455435777924691849641984 }, some { target := 197, numerator := 1769442549755569577447745650688 }, some { target := 199, numerator := 17656375757289122244102778257408 }, some { target := 207, numerator := 1769442549755569577447745650688 }, some { target := 214, numerator := 11082190778608164545262256128 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 11083459446870652212549255168 }, some { target := 509, numerator := 1769443190115264639649003339776 }, some { target := 511, numerator := 17656382147115905489014112649216 }, some { target := 519, numerator := 1769443190115264639649003339776 }, some { target := 526, numerator := 11082194789243213753830342656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 132368734070001434368147456 }, some { target := 907, numerator := 21132296843516016304578363392 }, some { target := 909, numerator := 210868543731604237309152591872 }, some { target := 917, numerator := 21132296843516016304578363392 }, some { target := 924, numerator := 132353630380582219234148352 }]

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

end Slot6

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent3
