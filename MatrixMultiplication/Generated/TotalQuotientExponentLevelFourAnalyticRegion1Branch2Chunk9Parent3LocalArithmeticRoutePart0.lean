import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk9Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 41; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 184867273914893170691276800 }, { target := 252, numerator := 6826902479849956042604544000 }, { target := 255, numerator := 6826900808113774362676428800 }, { target := 262, numerator := 184868945651074850619392000 }, { target := 466, numerator := 3704740169254459140653187072 }, { target := 468, numerator := 136811125696193119093795061760 }, { target := 471, numerator := 136811092194600038228035633152 }, { target := 478, numerator := 3704773670847540006412615680 }, { target := 562, numerator := 6218935094497006262054551552 }, { target := 564, numerator := 229656999422152521273216860160 }, { target := 567, numerator := 229656943184947369560435064832 }, { target := 574, numerator := 6218991331702157974836346880 }, { target := 597, numerator := 5967515601972751549914415104 }, { target := 599, numerator := 220372412049556581055274680320 }, { target := 602, numerator := 220372358085912636427195121664 }, { target := 609, numerator := 5967569565616696177993973760 }, { target := 613, numerator := 29371678002633553196278087680 }, { target := 616, numerator := 106831124249152505375201689600 }, { target := 618, numerator := 29371678002633553196278087680 }, { target := 733, numerator := 184867273914893170691276800 }, { target := 735, numerator := 6826902479849956042604544000 }, { target := 738, numerator := 6826900808113774362676428800 }, { target := 745, numerator := 184868945651074850619392000 }, { target := 829, numerator := 5967515601972751549914415104 }, { target := 831, numerator := 220372412049556581055274680320 }, { target := 834, numerator := 220372358085912636427195121664 }, { target := 841, numerator := 5967569565616696177993973760 }, { target := 864, numerator := 3985738425605096760103927808 }, { target := 866, numerator := 147188017465565052278553968640 }, { target := 869, numerator := 147187981422932975259303804928 }, { target := 876, numerator := 3985774468237173779354091520 }, { target := 880, numerator := 26846262697734219650429878272 }, { target := 883, numerator := 97645644407169299305558179840 }, { target := 885, numerator := 26846262697734219650429878272 }, { target := 925, numerator := 192261964871488897518927872 }, { target := 927, numerator := 7099978579043954284308725760 }, { target := 930, numerator := 7099976840438325337183485952 }, { target := 937, numerator := 192263703477117844644167680 }, { target := 960, numerator := 3704740169254459140653187072 }, { target := 962, numerator := 136811125696193119093795061760 }, { target := 965, numerator := 136811092194600038228035633152 }, { target := 972, numerator := 3704773670847540006412615680 }, { target := 976, numerator := 29371678002633553196278087680 }, { target := 979, numerator := 106831124249152505375201689600 }, { target := 981, numerator := 29371678002633553196278087680 }, { target := 986, numerator := 177472582958297443863625728 }, { target := 988, numerator := 6553826380655957800900362240 }, { target := 991, numerator := 6553824775789223388169371648 }, { target := 998, numerator := 177474187825031856594616320 }, { target := 1002, numerator := 26846262697734219650429878272 }, { target := 1005, numerator := 97645644407169299305558179840 }, { target := 1007, numerator := 26846262697734219650429878272 }, { target := 1012, numerator := 118842272105595403608187207680 }, { target := 1014, numerator := 118842215437197609172444643328 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk0

namespace RouteChunk1

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 51237676339135650568601600 }, { target := 122, numerator := 860792962497478929552506880 }, { target := 123, numerator := 1865051418744537680697098240 }, { target := 124, numerator := 61485211606962780682321920 }, { target := 125, numerator := 983763385711404490917150720 }, { target := 126, numerator := 71732746874789910796042240 }, { target := 127, numerator := 1865051418744537680697098240 }, { target := 128, numerator := 1865051418744537680697098240 }, { target := 129, numerator := 983763385711404490917150720 }, { target := 130, numerator := 23015964211539734235415838720 }, { target := 131, numerator := 1844556348208883420469657600 }, { target := 132, numerator := 860792962497478929552506880 }, { target := 133, numerator := 1865051418744537680697098240 }, { target := 134, numerator := 71732746874789910796042240 }, { target := 135, numerator := 1844556348208883420469657600 }, { target := 136, numerator := 71732746874789910796042240 }, { target := 137, numerator := 1865051418744537680697098240 }, { target := 138, numerator := 1865051418744537680697098240 }, { target := 139, numerator := 61485211606962780682321920 }, { target := 196, numerator := 52701609948825240584847360 }, { target := 197, numerator := 885387047140264041825435648 }, { target := 198, numerator := 1918338602137238757288443904 }, { target := 199, numerator := 63241931938590288701816832 }, { target := 200, numerator := 1011870911017444619229069312 }, { target := 201, numerator := 73782253928355336818786304 }, { target := 202, numerator := 1918338602137238757288443904 }, { target := 203, numerator := 1918338602137238757288443904 }, { target := 204, numerator := 1011870911017444619229069312 }, { target := 205, numerator := 23673563189012298070713434112 }, { target := 206, numerator := 1897257958157708661054504960 }, { target := 207, numerator := 885387047140264041825435648 }, { target := 208, numerator := 1918338602137238757288443904 }, { target := 209, numerator := 73782253928355336818786304 }, { target := 210, numerator := 1897257958157708661054504960 }, { target := 211, numerator := 73782253928355336818786304 }, { target := 212, numerator := 1918338602137238757288443904 }, { target := 213, numerator := 1918338602137238757288443904 }, { target := 214, numerator := 63241931938590288701816832 }, { target := 231, numerator := 51237676339135650568601600 }, { target := 232, numerator := 860792962497478929552506880 }, { target := 233, numerator := 1865051418744537680697098240 }, { target := 234, numerator := 61485211606962780682321920 }, { target := 235, numerator := 983763385711404490917150720 }, { target := 236, numerator := 71732746874789910796042240 }, { target := 237, numerator := 1865051418744537680697098240 }, { target := 238, numerator := 1865051418744537680697098240 }, { target := 239, numerator := 983763385711404490917150720 }, { target := 240, numerator := 23015964211539734235415838720 }, { target := 241, numerator := 1844556348208883420469657600 }, { target := 242, numerator := 860792962497478929552506880 }, { target := 243, numerator := 1865051418744537680697098240 }, { target := 244, numerator := 71732746874789910796042240 }, { target := 245, numerator := 1844556348208883420469657600 }, { target := 246, numerator := 71732746874789910796042240 }, { target := 247, numerator := 1865051418744537680697098240 }, { target := 248, numerator := 1865051418744537680697098240 }, { target := 249, numerator := 61485211606962780682321920 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk1

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 337, numerator := 45381941900377290503618560 }, { target := 338, numerator := 762416623926338480460791808 }, { target := 339, numerator := 1651902685173733374331715584 }, { target := 340, numerator := 54458330280452748604342272 }, { target := 341, numerator := 871333284487243977669476352 }, { target := 342, numerator := 63534718660528206705065984 }, { target := 343, numerator := 1651902685173733374331715584 }, { target := 344, numerator := 1651902685173733374331715584 }, { target := 345, numerator := 871333284487243977669476352 }, { target := 346, numerator := 20385568301649478894225457152 }, { target := 347, numerator := 1633749908413582458130268160 }, { target := 348, numerator := 762416623926338480460791808 }, { target := 349, numerator := 1651902685173733374331715584 }, { target := 350, numerator := 63534718660528206705065984 }, { target := 351, numerator := 1633749908413582458130268160 }, { target := 352, numerator := 63534718660528206705065984 }, { target := 353, numerator := 1651902685173733374331715584 }, { target := 354, numerator := 1651902685173733374331715584 }, { target := 355, numerator := 54458330280452748604342272 }, { target := 412, numerator := 2124167667659595113572597760 }, { target := 413, numerator := 35686016816681197908019642368 }, { target := 414, numerator := 77319703102809262134042558464 }, { target := 415, numerator := 2549001201191514136287117312 }, { target := 416, numerator := 40784019219064226180593876992 }, { target := 417, numerator := 2973834734723433159001636864 }, { target := 418, numerator := 77319703102809262134042558464 }, { target := 419, numerator := 77319703102809262134042558464 }, { target := 420, numerator := 40784019219064226180593876992 }, { target := 421, numerator := 954176116312690125016810913792 }, { target := 422, numerator := 76470036035745424088613519360 }, { target := 423, numerator := 35686016816681197908019642368 }, { target := 424, numerator := 77319703102809262134042558464 }, { target := 425, numerator := 2973834734723433159001636864 }, { target := 426, numerator := 76470036035745424088613519360 }, { target := 427, numerator := 2973834734723433159001636864 }, { target := 428, numerator := 77319703102809262134042558464 }, { target := 429, numerator := 77319703102809262134042558464 }, { target := 430, numerator := 2549001201191514136287117312 }, { target := 447, numerator := 578253775827388056417075200 }, { target := 448, numerator := 9714663433900119347806863360 }, { target := 449, numerator := 21048437440116925253581537280 }, { target := 450, numerator := 693904530992865667700490240 }, { target := 451, numerator := 11102472495885850683207843840 }, { target := 452, numerator := 809555286158343278983905280 }, { target := 453, numerator := 21048437440116925253581537280 }, { target := 454, numerator := 21048437440116925253581537280 }, { target := 455, numerator := 11102472495885850683207843840 }, { target := 456, numerator := 259751596101662714942550179840 }, { target := 457, numerator := 20817135929785970031014707200 }, { target := 458, numerator := 9714663433900119347806863360 }, { target := 459, numerator := 21048437440116925253581537280 }, { target := 460, numerator := 809555286158343278983905280 }, { target := 461, numerator := 20817135929785970031014707200 }, { target := 462, numerator := 809555286158343278983905280 }, { target := 463, numerator := 21048437440116925253581537280 }, { target := 464, numerator := 21048437440116925253581537280 }, { target := 465, numerator := 693904530992865667700490240 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

namespace RouteChunk3

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 508, numerator := 52701609948825240584847360 }, { target := 509, numerator := 885387047140264041825435648 }, { target := 510, numerator := 1918338602137238757288443904 }, { target := 511, numerator := 63241931938590288701816832 }, { target := 512, numerator := 1011870911017444619229069312 }, { target := 513, numerator := 73782253928355336818786304 }, { target := 514, numerator := 1918338602137238757288443904 }, { target := 515, numerator := 1918338602137238757288443904 }, { target := 516, numerator := 1011870911017444619229069312 }, { target := 517, numerator := 23673563189012298070713434112 }, { target := 518, numerator := 1897257958157708661054504960 }, { target := 519, numerator := 885387047140264041825435648 }, { target := 520, numerator := 1918338602137238757288443904 }, { target := 521, numerator := 73782253928355336818786304 }, { target := 522, numerator := 1897257958157708661054504960 }, { target := 523, numerator := 73782253928355336818786304 }, { target := 524, numerator := 1918338602137238757288443904 }, { target := 525, numerator := 1918338602137238757288443904 }, { target := 526, numerator := 63241931938590288701816832 }, { target := 543, numerator := 2124167667659595113572597760 }, { target := 544, numerator := 35686016816681197908019642368 }, { target := 545, numerator := 77319703102809262134042558464 }, { target := 546, numerator := 2549001201191514136287117312 }, { target := 547, numerator := 40784019219064226180593876992 }, { target := 548, numerator := 2973834734723433159001636864 }, { target := 549, numerator := 77319703102809262134042558464 }, { target := 550, numerator := 77319703102809262134042558464 }, { target := 551, numerator := 40784019219064226180593876992 }, { target := 552, numerator := 954176116312690125016810913792 }, { target := 553, numerator := 76470036035745424088613519360 }, { target := 554, numerator := 35686016816681197908019642368 }, { target := 555, numerator := 77319703102809262134042558464 }, { target := 556, numerator := 2973834734723433159001636864 }, { target := 557, numerator := 76470036035745424088613519360 }, { target := 558, numerator := 2973834734723433159001636864 }, { target := 559, numerator := 77319703102809262134042558464 }, { target := 560, numerator := 77319703102809262134042558464 }, { target := 561, numerator := 2549001201191514136287117312 }, { target := 578, numerator := 51237676339135650568601600 }, { target := 579, numerator := 860792962497478929552506880 }, { target := 580, numerator := 1865051418744537680697098240 }, { target := 581, numerator := 61485211606962780682321920 }, { target := 582, numerator := 983763385711404490917150720 }, { target := 583, numerator := 71732746874789910796042240 }, { target := 584, numerator := 1865051418744537680697098240 }, { target := 585, numerator := 1865051418744537680697098240 }, { target := 586, numerator := 983763385711404490917150720 }, { target := 587, numerator := 23015964211539734235415838720 }, { target := 588, numerator := 1844556348208883420469657600 }, { target := 589, numerator := 860792962497478929552506880 }, { target := 590, numerator := 1865051418744537680697098240 }, { target := 591, numerator := 71732746874789910796042240 }, { target := 592, numerator := 1844556348208883420469657600 }, { target := 593, numerator := 71732746874789910796042240 }, { target := 594, numerator := 1865051418744537680697098240 }, { target := 595, numerator := 1865051418744537680697098240 }, { target := 596, numerator := 61485211606962780682321920 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk3

namespace RouteChunk4

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 679, numerator := 51237676339135650568601600 }, { target := 680, numerator := 860792962497478929552506880 }, { target := 681, numerator := 1865051418744537680697098240 }, { target := 682, numerator := 61485211606962780682321920 }, { target := 683, numerator := 983763385711404490917150720 }, { target := 684, numerator := 71732746874789910796042240 }, { target := 685, numerator := 1865051418744537680697098240 }, { target := 686, numerator := 1865051418744537680697098240 }, { target := 687, numerator := 983763385711404490917150720 }, { target := 688, numerator := 23015964211539734235415838720 }, { target := 689, numerator := 1844556348208883420469657600 }, { target := 690, numerator := 860792962497478929552506880 }, { target := 691, numerator := 1865051418744537680697098240 }, { target := 692, numerator := 71732746874789910796042240 }, { target := 693, numerator := 1844556348208883420469657600 }, { target := 694, numerator := 71732746874789910796042240 }, { target := 695, numerator := 1865051418744537680697098240 }, { target := 696, numerator := 1865051418744537680697098240 }, { target := 697, numerator := 61485211606962780682321920 }, { target := 714, numerator := 43918008290687700487372800 }, { target := 715, numerator := 737822539283553368187863040 }, { target := 716, numerator := 1598615501781032297740369920 }, { target := 717, numerator := 52701609948825240584847360 }, { target := 718, numerator := 843225759181203849357557760 }, { target := 719, numerator := 61485211606962780682321920 }, { target := 720, numerator := 1598615501781032297740369920 }, { target := 721, numerator := 1598615501781032297740369920 }, { target := 722, numerator := 843225759181203849357557760 }, { target := 723, numerator := 19727969324176915058927861760 }, { target := 724, numerator := 1581048298464757217545420800 }, { target := 725, numerator := 737822539283553368187863040 }, { target := 726, numerator := 1598615501781032297740369920 }, { target := 727, numerator := 61485211606962780682321920 }, { target := 728, numerator := 1581048298464757217545420800 }, { target := 729, numerator := 61485211606962780682321920 }, { target := 730, numerator := 1598615501781032297740369920 }, { target := 731, numerator := 1598615501781032297740369920 }, { target := 732, numerator := 52701609948825240584847360 }, { target := 775, numerator := 51237676339135650568601600 }, { target := 776, numerator := 860792962497478929552506880 }, { target := 777, numerator := 1865051418744537680697098240 }, { target := 778, numerator := 61485211606962780682321920 }, { target := 779, numerator := 983763385711404490917150720 }, { target := 780, numerator := 71732746874789910796042240 }, { target := 781, numerator := 1865051418744537680697098240 }, { target := 782, numerator := 1865051418744537680697098240 }, { target := 783, numerator := 983763385711404490917150720 }, { target := 784, numerator := 23015964211539734235415838720 }, { target := 785, numerator := 1844556348208883420469657600 }, { target := 786, numerator := 860792962497478929552506880 }, { target := 787, numerator := 1865051418744537680697098240 }, { target := 788, numerator := 71732746874789910796042240 }, { target := 789, numerator := 1844556348208883420469657600 }, { target := 790, numerator := 71732746874789910796042240 }, { target := 791, numerator := 1865051418744537680697098240 }, { target := 792, numerator := 1865051418744537680697098240 }, { target := 793, numerator := 61485211606962780682321920 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk4

namespace RouteChunk5

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 810, numerator := 578253775827388056417075200 }, { target := 811, numerator := 9714663433900119347806863360 }, { target := 812, numerator := 21048437440116925253581537280 }, { target := 813, numerator := 693904530992865667700490240 }, { target := 814, numerator := 11102472495885850683207843840 }, { target := 815, numerator := 809555286158343278983905280 }, { target := 816, numerator := 21048437440116925253581537280 }, { target := 817, numerator := 21048437440116925253581537280 }, { target := 818, numerator := 11102472495885850683207843840 }, { target := 819, numerator := 259751596101662714942550179840 }, { target := 820, numerator := 20817135929785970031014707200 }, { target := 821, numerator := 9714663433900119347806863360 }, { target := 822, numerator := 21048437440116925253581537280 }, { target := 823, numerator := 809555286158343278983905280 }, { target := 824, numerator := 20817135929785970031014707200 }, { target := 825, numerator := 809555286158343278983905280 }, { target := 826, numerator := 21048437440116925253581537280 }, { target := 827, numerator := 21048437440116925253581537280 }, { target := 828, numerator := 693904530992865667700490240 }, { target := 845, numerator := 43918008290687700487372800 }, { target := 846, numerator := 737822539283553368187863040 }, { target := 847, numerator := 1598615501781032297740369920 }, { target := 848, numerator := 52701609948825240584847360 }, { target := 849, numerator := 843225759181203849357557760 }, { target := 850, numerator := 61485211606962780682321920 }, { target := 851, numerator := 1598615501781032297740369920 }, { target := 852, numerator := 1598615501781032297740369920 }, { target := 853, numerator := 843225759181203849357557760 }, { target := 854, numerator := 19727969324176915058927861760 }, { target := 855, numerator := 1581048298464757217545420800 }, { target := 856, numerator := 737822539283553368187863040 }, { target := 857, numerator := 1598615501781032297740369920 }, { target := 858, numerator := 61485211606962780682321920 }, { target := 859, numerator := 1581048298464757217545420800 }, { target := 860, numerator := 61485211606962780682321920 }, { target := 861, numerator := 1598615501781032297740369920 }, { target := 862, numerator := 1598615501781032297740369920 }, { target := 863, numerator := 52701609948825240584847360 }, { target := 906, numerator := 51237676339135650568601600 }, { target := 907, numerator := 860792962497478929552506880 }, { target := 908, numerator := 1865051418744537680697098240 }, { target := 909, numerator := 61485211606962780682321920 }, { target := 910, numerator := 983763385711404490917150720 }, { target := 911, numerator := 71732746874789910796042240 }, { target := 912, numerator := 1865051418744537680697098240 }, { target := 913, numerator := 1865051418744537680697098240 }, { target := 914, numerator := 983763385711404490917150720 }, { target := 915, numerator := 23015964211539734235415838720 }, { target := 916, numerator := 1844556348208883420469657600 }, { target := 917, numerator := 860792962497478929552506880 }, { target := 918, numerator := 1865051418744537680697098240 }, { target := 919, numerator := 71732746874789910796042240 }, { target := 920, numerator := 1844556348208883420469657600 }, { target := 921, numerator := 71732746874789910796042240 }, { target := 922, numerator := 1865051418744537680697098240 }, { target := 923, numerator := 1865051418744537680697098240 }, { target := 924, numerator := 61485211606962780682321920 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk5

namespace RouteChunk6

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left7.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 132372745162728955067760640 }, { target := 122, numerator := 21132937203211078505836052480 }, { target := 124, numerator := 210874933558387482220486983680 }, { target := 132, numerator := 21132937203211078505836052480 }, { target := 139, numerator := 132357641015631427802234880 }, { target := 196, numerator := 11083455435777924691849641984 }, { target := 197, numerator := 1769442549755569577447745650688 }, { target := 199, numerator := 17656375757289122244102778257408 }, { target := 207, numerator := 1769442549755569577447745650688 }, { target := 214, numerator := 11082190778608164545262256128 }, { target := 250, numerator := 8788250473069785425274470400 }, { target := 252, numerator := 330197146648437813467204812800 }, { target := 255, numerator := 330172173139671985847638425600 }, { target := 262, numerator := 8813223981835613044840857600 }, { target := 508, numerator := 11083459446870652212549255168 }, { target := 509, numerator := 1769443190115264639649003339776 }, { target := 511, numerator := 17656382147115905489014112649216 }, { target := 519, numerator := 1769443190115264639649003339776 }, { target := 526, numerator := 11082194789243213753830342656 }, { target := 562, numerator := 85123636376716325398826188800 }, { target := 564, numerator := 3198313695093485356493412761600 }, { target := 567, numerator := 3198071799862375667658339123200 }, { target := 574, numerator := 85365531607826014233899827200 }, { target := 613, numerator := 43749703149238226331956674560 }, { target := 616, numerator := 150185081244316560116718501888 }, { target := 618, numerator := 43749703149238226331956674560 }, { target := 880, numerator := 43749703149238226331956674560 }, { target := 883, numerator := 150185081244316560116718501888 }, { target := 885, numerator := 43749703149238226331956674560 }, { target := 906, numerator := 132368734070001434368147456 }, { target := 907, numerator := 21132296843516016304578363392 }, { target := 909, numerator := 210868543731604237309152591872 }, { target := 917, numerator := 21132296843516016304578363392 }, { target := 924, numerator := 132353630380582219234148352 }, { target := 925, numerator := 8788250473069785425274470400 }, { target := 927, numerator := 330197146648437813467204812800 }, { target := 930, numerator := 330172173139671985847638425600 }, { target := 937, numerator := 8813223981835613044840857600 }, { target := 941, numerator := 45381941900377290503618560 }, { target := 942, numerator := 762416623926338480460791808 }, { target := 943, numerator := 1651902685173733374331715584 }, { target := 944, numerator := 54458330280452748604342272 }, { target := 945, numerator := 871333284487243977669476352 }, { target := 946, numerator := 63534718660528206705065984 }, { target := 947, numerator := 1651902685173733374331715584 }, { target := 948, numerator := 1651902685173733374331715584 }, { target := 949, numerator := 871333284487243977669476352 }, { target := 950, numerator := 20385568301649478894225457152 }, { target := 951, numerator := 1633749908413582458130268160 }, { target := 952, numerator := 762416623926338480460791808 }, { target := 953, numerator := 1651902685173733374331715584 }, { target := 954, numerator := 63534718660528206705065984 }, { target := 955, numerator := 1633749908413582458130268160 }, { target := 956, numerator := 63534718660528206705065984 }, { target := 957, numerator := 1651902685173733374331715584 }, { target := 958, numerator := 1651902685173733374331715584 }, { target := 959, numerator := 54458330280452748604342272 }, { target := 976, numerator := 43749703149238226331956674560 }, { target := 979, numerator := 150185081244316560116718501888 }, { target := 981, numerator := 43749703149238226331956674560 }, { target := 1002, numerator := 43749703149238226331956674560 }, { target := 1005, numerator := 150185081244316560116718501888 }, { target := 1007, numerator := 43749703149238226331956674560 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk6

namespace RouteChunk7

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 168006563602818597220515840 }, { target := 35, numerator := 130671771691081131171512320 }, { target := 36, numerator := 149339167646949864196014080 }, { target := 37, numerator := 175473521985166090430316544 }, { target := 38, numerator := 2072080951101429365719695360 }, { target := 39, numerator := 4659382030584835762915639296 }, { target := 40, numerator := 130671771691081131171512320 }, { target := 41, numerator := 2072080951101429365719695360 }, { target := 42, numerator := 149339167646949864196014080 }, { target := 43, numerator := 145605688455776117591113728 }, { target := 44, numerator := 145605688455776117591113728 }, { target := 45, numerator := 145605688455776117591113728 }, { target := 46, numerator := 4659382030584835762915639296 }, { target := 47, numerator := 145605688455776117591113728 }, { target := 48, numerator := 168006563602818597220515840 }, { target := 49, numerator := 175473521985166090430316544 }, { target := 79, numerator := 17615185182637458770897141760 }, { target := 80, numerator := 13700699586495801266253332480 }, { target := 81, numerator := 15657942384566630018575237120 }, { target := 82, numerator := 18398082301865790271825903616 }, { target := 83, numerator := 217253950585861991507731415040 }, { target := 84, numerator := 488527802398478856579547398144 }, { target := 85, numerator := 13700699586495801266253332480 }, { target := 86, numerator := 217253950585861991507731415040 }, { target := 87, numerator := 15657942384566630018575237120 }, { target := 88, numerator := 15266493824952464268110856192 }, { target := 89, numerator := 15266493824952464268110856192 }, { target := 90, numerator := 15266493824952464268110856192 }, { target := 91, numerator := 488527802398478856579547398144 }, { target := 92, numerator := 15266493824952464268110856192 }, { target := 93, numerator := 17615185182637458770897141760 }, { target := 94, numerator := 18398082301865790271825903616 }, { target := 154, numerator := 189874089911955357570170880000 }, { target := 155, numerator := 147679847709298611443466240000 }, { target := 156, numerator := 168776968810626984506818560000 }, { target := 157, numerator := 198312938352486706795511808000 }, { target := 158, numerator := 2341780442247449410032107520000 }, { target := 159, numerator := 5265841426891561916612739072000 }, { target := 160, numerator := 147679847709298611443466240000 }, { target := 161, numerator := 2341780442247449410032107520000 }, { target := 162, numerator := 168776968810626984506818560000 }, { target := 163, numerator := 164557544590361309894148096000 }, { target := 164, numerator := 164557544590361309894148096000 }, { target := 165, numerator := 164557544590361309894148096000 }, { target := 166, numerator := 5265841426891561916612739072000 }, { target := 167, numerator := 164557544590361309894148096000 }, { target := 168, numerator := 189874089911955357570170880000 }, { target := 169, numerator := 198312938352486706795511808000 }, { target := 492, numerator := 17615198619937594963698647040 }, { target := 493, numerator := 13700710037729240527321169920 }, { target := 494, numerator := 15657954328833417745509908480 }, { target := 495, numerator := 18398096336379265850974142464 }, { target := 496, numerator := 217254116312563671218949980160 }, { target := 497, numerator := 488528175059602633659909144576 }, { target := 498, numerator := 13700710037729240527321169920 }, { target := 499, numerator := 217254116312563671218949980160 }, { target := 500, numerator := 15657954328833417745509908480 }, { target := 501, numerator := 15266505470612582301872160768 }, { target := 502, numerator := 15266505470612582301872160768 }, { target := 503, numerator := 15266505470612582301872160768 }, { target := 504, numerator := 488528175059602633659909144576 }, { target := 505, numerator := 15266505470612582301872160768 }, { target := 506, numerator := 17615198619937594963698647040 }, { target := 507, numerator := 18398096336379265850974142464 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk7

namespace RouteChunk8

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 200236449732752861571317760 }, { target := 122, numerator := 29573875749208654629474140160 }, { target := 124, numerator := 308243561045464791017481830400 }, { target := 132, numerator := 29573875749208654629474140160 }, { target := 139, numerator := 200236449732752861571317760 }, { target := 250, numerator := 555503618498838914068905984 }, { target := 252, numerator := 20131635006746695523503177728 }, { target := 255, numerator := 20131642405043990585640222720 }, { target := 262, numerator := 555496220201543851931860992 }, { target := 466, numerator := 13296247900843176588358975488 }, { target := 468, numerator := 481860425000195099304495415296 }, { target := 471, numerator := 481860602082020677888549847040 }, { target := 478, numerator := 13296070819017598004304543744 }, { target := 562, numerator := 9945306718285664429298155520 }, { target := 564, numerator := 360421207378852129533685923840 }, { target := 567, numerator := 360421339832239186291300761600 }, { target := 574, numerator := 9945174264898607671683317760 }, { target := 597, numerator := 11540139687524266472915337216 }, { target := 599, numerator := 418218482075641029585033756672 }, { target := 602, numerator := 418218635769300965714590433280 }, { target := 609, numerator := 11539985993864330343358660608 }, { target := 733, numerator := 555503618498838914068905984 }, { target := 735, numerator := 20131635006746695523503177728 }, { target := 738, numerator := 20131642405043990585640222720 }, { target := 745, numerator := 555496220201543851931860992 }, { target := 829, numerator := 11522220215959787798267953152 }, { target := 831, numerator := 417569074494778232955243331584 }, { target := 834, numerator := 417569227949783417631182684160 }, { target := 841, numerator := 11522066760954603122328600576 }, { target := 864, numerator := 11575978630653223822210105344 }, { target := 866, numerator := 419517297237366622844614606848 }, { target := 869, numerator := 419517451408336061881405931520 }, { target := 876, numerator := 11575824459683784785418780672 }, { target := 890, numerator := 168006563602818597220515840 }, { target := 891, numerator := 130671771691081131171512320 }, { target := 892, numerator := 149339167646949864196014080 }, { target := 893, numerator := 175473521985166090430316544 }, { target := 894, numerator := 2072080951101429365719695360 }, { target := 895, numerator := 4659382030584835762915639296 }, { target := 896, numerator := 130671771691081131171512320 }, { target := 897, numerator := 2072080951101429365719695360 }, { target := 898, numerator := 149339167646949864196014080 }, { target := 899, numerator := 145605688455776117591113728 }, { target := 900, numerator := 145605688455776117591113728 }, { target := 901, numerator := 145605688455776117591113728 }, { target := 902, numerator := 4659382030584835762915639296 }, { target := 903, numerator := 145605688455776117591113728 }, { target := 904, numerator := 168006563602818597220515840 }, { target := 905, numerator := 175473521985166090430316544 }, { target := 925, numerator := 555503618498838914068905984 }, { target := 927, numerator := 20131635006746695523503177728 }, { target := 930, numerator := 20131642405043990585640222720 }, { target := 937, numerator := 555496220201543851931860992 }, { target := 960, numerator := 13296247900843176588358975488 }, { target := 962, numerator := 481860425000195099304495415296 }, { target := 965, numerator := 481860602082020677888549847040 }, { target := 972, numerator := 13296070819017598004304543744 }, { target := 986, numerator := 555503618498838914068905984 }, { target := 988, numerator := 20131635006746695523503177728 }, { target := 991, numerator := 20131642405043990585640222720 }, { target := 998, numerator := 555496220201543851931860992 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk8

namespace RouteChunk9

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 571605172658225549259309056 }, { target := 11, numerator := 13681646390722688953238945792 }, { target := 12, numerator := 10233576478235973543190855680 }, { target := 13, numerator := 11874636490061201732999839744 }, { target := 14, numerator := 571605172658225549259309056 }, { target := 15, numerator := 11856197613523839618507603968 }, { target := 16, numerator := 11911514243135925961984311296 }, { target := 17, numerator := 571605172658225549259309056 }, { target := 18, numerator := 13681646390722688953238945792 }, { target := 19, numerator := 571605172658225549259309056 }, { target := 34, numerator := 201757232895280098494644224 }, { target := 35, numerator := 16965612758008192975501262848 }, { target := 40, numerator := 16965608664988232833491271680 }, { target := 48, numerator := 201761325915240240504635392 }, { target := 55, numerator := 20715160659116164958967037952 }, { target := 56, numerator := 495827393840780464501727166464 }, { target := 57, numerator := 370868198897079727491184066560 }, { target := 58, numerator := 430340756918413233341121691648 }, { target := 59, numerator := 20715160659116164958967037952 }, { target := 60, numerator := 429672525929409486084380819456 }, { target := 61, numerator := 431677218896420727854603436032 }, { target := 62, numerator := 20715160659116164958967037952 }, { target := 63, numerator := 495827393840780464501727166464 }, { target := 64, numerator := 20715160659116164958967037952 }, { target := 79, numerator := 29798487463759606436786601984 }, { target := 80, numerator := 2505732220003766661314005434368 }, { target := 85, numerator := 2505731615486138118526866554880 }, { target := 93, numerator := 29799091981388149223925481472 }, { target := 154, numerator := 310584651382518953987234856960 }, { target := 155, numerator := 26116827874377827926593681489920 }, { target := 160, numerator := 26116821573591684203976799027200 }, { target := 168, numerator := 310590952168662676604117319680 }, { target := 196, numerator := 16837731254807126194278891520 }, { target := 197, numerator := 2486844791209768420148321976320 }, { target := 199, numerator := 25919967362761914650765085900800 }, { target := 207, numerator := 2486844791209768420148321976320 }, { target := 214, numerator := 16837731254807126194278891520 }, { target := 492, numerator := 29798487463759606436786601984 }, { target := 493, numerator := 2505732220003766661314005434368 }, { target := 498, numerator := 2505731615486138118526866554880 }, { target := 506, numerator := 29799091981388149223925481472 }, { target := 508, numerator := 16837727192639075299570483200 }, { target := 509, numerator := 2486844191248805419140985651200 }, { target := 511, numerator := 25919961109469133820529737728000 }, { target := 519, numerator := 2486844191248805419140985651200 }, { target := 526, numerator := 16837727192639075299570483200 }, { target := 890, numerator := 201757232895280098494644224 }, { target := 891, numerator := 16965612758008192975501262848 }, { target := 896, numerator := 16965608664988232833491271680 }, { target := 904, numerator := 201761325915240240504635392 }, { target := 906, numerator := 200240511900803756279726080 }, { target := 907, numerator := 29574475710171655636810465280 }, { target := 909, numerator := 308249814338245621252830003200 }, { target := 917, numerator := 29574475710171655636810465280 }, { target := 924, numerator := 200240511900803756279726080 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk9

namespace RouteChunk10

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected,
    Slot12.Left6.expected,
    Slot12.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 164114519658351757130465280 }, { target := 122, numerator := 17207111394622691386243153920 }, { target := 124, numerator := 185475462346427434228776960000 }, { target := 132, numerator := 17207124520634021335195975680 }, { target := 139, numerator := 164114519658351757130465280 }, { target := 144, numerator := 20715168271856859877977620480 }, { target := 145, numerator := 495827576055412581595464335360 }, { target := 146, numerator := 370868335189695394589599334400 }, { target := 147, numerator := 430340915066961863271535083520 }, { target := 148, numerator := 20715168271856859877977620480 }, { target := 149, numerator := 429672683832385835533535805440 }, { target := 150, numerator := 431677377536113918747533639680 }, { target := 151, numerator := 20715168271856859877977620480 }, { target := 152, numerator := 495827576055412581595464335360 }, { target := 153, numerator := 20715168271856859877977620480 }, { target := 196, numerator := 127644626400940255545917440 }, { target := 197, numerator := 13383308862484315522633564160 }, { target := 199, numerator := 144258692936110226622382080000 }, { target := 207, numerator := 13383319071604238816263536640 }, { target := 214, numerator := 127644626400940255545917440 }, { target := 231, numerator := 145879573029646006338191360 }, { target := 232, numerator := 15295210128553503454438359040 }, { target := 234, numerator := 164867077641268830425579520000 }, { target := 242, numerator := 15295221796119130075729756160 }, { target := 249, numerator := 145879573029646006338191360 }, { target := 337, numerator := 171408498309834057447374848 }, { target := 338, numerator := 17971871901050366558965071872 }, { target := 340, numerator := 193718816228490875750055936000 }, { target := 348, numerator := 17971885610439977838982463488 }, { target := 355, numerator := 171408498309834057447374848 }, { target := 412, numerator := 2024079075786338337942405120 }, { target := 413, numerator := 212221040533679860430332231680 }, { target := 415, numerator := 2287530702272605022154915840000 }, { target := 423, numerator := 212221202421152929800750366720 }, { target := 430, numerator := 2024079075786338337942405120 }, { target := 447, numerator := 4551442678524955397751570432 }, { target := 448, numerator := 477210556010869307778476802048 }, { target := 450, numerator := 5143852822407587509278081024000 }, { target := 458, numerator := 477210920038916858362768392192 }, { target := 465, numerator := 4551442678524955397751570432 }, { target := 482, numerator := 571597559917530630248726528 }, { target := 483, numerator := 13681464176090571859501776896 }, { target := 484, numerator := 10233440185620306444775587840 }, { target := 485, numerator := 11874478341512571802586447872 }, { target := 486, numerator := 571597559917530630248726528 }, { target := 487, numerator := 11856039710547490169352617984 }, { target := 488, numerator := 11911355603442735069054107648 }, { target := 489, numerator := 571597559917530630248726528 }, { target := 490, numerator := 13681464176090571859501776896 }, { target := 491, numerator := 571597559917530630248726528 }, { target := 508, numerator := 127644626400940255545917440 }, { target := 509, numerator := 13383308862484315522633564160 }, { target := 511, numerator := 144258692936110226622382080000 }, { target := 519, numerator := 13383319071604238816263536640 }, { target := 526, numerator := 127644626400940255545917440 }, { target := 543, numerator := 2024079075786338337942405120 }, { target := 544, numerator := 212221040533679860430332231680 }, { target := 546, numerator := 2287530702272605022154915840000 }, { target := 554, numerator := 212221202421152929800750366720 }, { target := 561, numerator := 2024079075786338337942405120 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk10

namespace RouteChunk11

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot12.Left8.expected,
    Slot12.Left9.expected,
    Slot12.Left10.expected,
    Slot12.Left11.expected,
    Slot12.Left12.expected,
    Slot12.Left13.expected,
    Slot12.Left14.expected,
    Slot12.Left15.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 8524602958877691862516236288 }, { target := 12, numerator := 82569927285414835636861403136 }, { target := 17, numerator := 8524602958877691862516236288 }, { target := 34, numerator := 131395824534221730307112960 }, { target := 35, numerator := 11001658716694692775304626176 }, { target := 40, numerator := 11001662698185259945297969152 }, { target := 48, numerator := 131391843043654560313769984 }, { target := 79, numerator := 20976974567025018885866782720 }, { target := 80, numerator := 1756383933152207440344810258432 }, { target := 85, numerator := 1756384568786000693968936894464 }, { target := 93, numerator := 20976338933231765261740146688 }, { target := 154, numerator := 209318660986000858735464939520 }, { target := 155, numerator := 17526070401146767098389842624512 }, { target := 160, numerator := 17526076743816157109021388570624 }, { target := 168, numerator := 209312318316610848103918993408 }, { target := 492, numerator := 20976974567025018885866782720 }, { target := 493, numerator := 1756383933152207440344810258432 }, { target := 498, numerator := 1756384568786000693968936894464 }, { target := 506, numerator := 20976338933231765261740146688 }, { target := 578, numerator := 145879573029646006338191360 }, { target := 579, numerator := 15295210128553503454438359040 }, { target := 581, numerator := 164867077641268830425579520000 }, { target := 589, numerator := 15295221796119130075729756160 }, { target := 596, numerator := 145879573029646006338191360 }, { target := 679, numerator := 142232583703904856179736576 }, { target := 680, numerator := 14912829875339665868077400064 }, { target := 682, numerator := 160745400700237109664940032000 }, { target := 690, numerator := 14912841251216151823836512256 }, { target := 697, numerator := 142232583703904856179736576 }, { target := 714, numerator := 142232583703904856179736576 }, { target := 715, numerator := 14912829875339665868077400064 }, { target := 717, numerator := 160745400700237109664940032000 }, { target := 725, numerator := 14912841251216151823836512256 }, { target := 732, numerator := 142232583703904856179736576 }, { target := 775, numerator := 142232583703904856179736576 }, { target := 776, numerator := 14912829875339665868077400064 }, { target := 778, numerator := 160745400700237109664940032000 }, { target := 786, numerator := 14912841251216151823836512256 }, { target := 793, numerator := 142232583703904856179736576 }, { target := 810, numerator := 4551442678524955397751570432 }, { target := 811, numerator := 477210556010869307778476802048 }, { target := 813, numerator := 5143852822407587509278081024000 }, { target := 821, numerator := 477210920038916858362768392192 }, { target := 828, numerator := 4551442678524955397751570432 }, { target := 845, numerator := 142232583703904856179736576 }, { target := 846, numerator := 14912829875339665868077400064 }, { target := 848, numerator := 160745400700237109664940032000 }, { target := 856, numerator := 14912841251216151823836512256 }, { target := 863, numerator := 142232583703904856179736576 }, { target := 890, numerator := 131380831856844479995576320 }, { target := 891, numerator := 11000403392788178091053678592 }, { target := 896, numerator := 11000407373824444648636022784 }, { target := 904, numerator := 131376850820577922413232128 }, { target := 906, numerator := 164114519658351757130465280 }, { target := 907, numerator := 17207111394622691386243153920 }, { target := 909, numerator := 185475462346427434228776960000 }, { target := 917, numerator := 17207124520634021335195975680 }, { target := 924, numerator := 164114519658351757130465280 }, { target := 941, numerator := 171408498309834057447374848 }, { target := 942, numerator := 17971871901050366558965071872 }, { target := 944, numerator := 193718816228490875750055936000 }, { target := 952, numerator := 17971885610439977838982463488 }, { target := 959, numerator := 171408498309834057447374848 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk11

namespace RouteChunk12

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 43749703149238226331956674560 }, { target := 2, numerator := 43749703149238226331956674560 }, { target := 3, numerator := 43749703149238226331956674560 }, { target := 4, numerator := 43749703149238226331956674560 }, { target := 34, numerator := 52064090473637838480998400 }, { target := 35, numerator := 53551635915741776723312640 }, { target := 36, numerator := 52064090473637838480998400 }, { target := 37, numerator := 46113908705222085511741440 }, { target := 38, numerator := 2158428436492814389597962240 }, { target := 39, numerator := 587580449631055605714124800 }, { target := 40, numerator := 53551635915741776723312640 }, { target := 41, numerator := 2158428436492814389597962240 }, { target := 42, numerator := 52064090473637838480998400 }, { target := 43, numerator := 52064090473637838480998400 }, { target := 44, numerator := 44626363263118147269427200 }, { target := 45, numerator := 52064090473637838480998400 }, { target := 46, numerator := 587580449631055605714124800 }, { target := 47, numerator := 44626363263118147269427200 }, { target := 48, numerator := 52064090473637838480998400 }, { target := 49, numerator := 46113908705222085511741440 }, { target := 51, numerator := 150185081244316560116718501888 }, { target := 52, numerator := 150185081244316560116718501888 }, { target := 53, numerator := 150185081244316560116718501888 }, { target := 54, numerator := 150185081244316560116718501888 }, { target := 55, numerator := 320291232248984679063188668416 }, { target := 57, numerator := 3102364284240680795798610378752 }, { target := 62, numerator := 320291232248984679063188668416 }, { target := 79, numerator := 874676719957115686480773120 }, { target := 80, numerator := 899667483384461848951652352 }, { target := 81, numerator := 874676719957115686480773120 }, { target := 82, numerator := 774713666247731036597256192 }, { target := 83, numerator := 36261597733079281745245765632 }, { target := 84, numerator := 9871351553801734175997296640 }, { target := 85, numerator := 899667483384461848951652352 }, { target := 86, numerator := 36261597733079281745245765632 }, { target := 87, numerator := 874676719957115686480773120 }, { target := 88, numerator := 874676719957115686480773120 }, { target := 89, numerator := 749722902820384874126376960 }, { target := 90, numerator := 874676719957115686480773120 }, { target := 91, numerator := 9871351553801734175997296640 }, { target := 92, numerator := 749722902820384874126376960 }, { target := 93, numerator := 874676719957115686480773120 }, { target := 94, numerator := 774713666247731036597256192 }, { target := 140, numerator := 43749703149238226331956674560 }, { target := 141, numerator := 43749703149238226331956674560 }, { target := 142, numerator := 43749703149238226331956674560 }, { target := 143, numerator := 43749703149238226331956674560 }, { target := 144, numerator := 320267007945481826272209272832 }, { target := 146, numerator := 3102129645866504397628588949504 }, { target := 151, numerator := 320267007945481826272209272832 }, { target := 482, numerator := 8548827262380544653495631872 }, { target := 484, numerator := 82804565659591233806882832384 }, { target := 489, numerator := 8548827262380544653495631872 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk12

namespace RouteChunk13

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot16.Left2.expected,
    Slot16.Left3.expected,
    Slot16.Left4.expected,
    Slot16.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 105, numerator := 1895132893240417320708341760 }, { target := 106, numerator := 1949279547333000672728580096 }, { target := 107, numerator := 1895132893240417320708341760 }, { target := 108, numerator := 1678546276870083912627388416 }, { target := 109, numerator := 78566795088338443781365825536 }, { target := 110, numerator := 21387928366570424047994142720 }, { target := 111, numerator := 1949279547333000672728580096 }, { target := 112, numerator := 78566795088338443781365825536 }, { target := 113, numerator := 1895132893240417320708341760 }, { target := 114, numerator := 1895132893240417320708341760 }, { target := 115, numerator := 1624399622777500560607150080 }, { target := 116, numerator := 1895132893240417320708341760 }, { target := 117, numerator := 21387928366570424047994142720 }, { target := 118, numerator := 1624399622777500560607150080 }, { target := 119, numerator := 1895132893240417320708341760 }, { target := 120, numerator := 1678546276870083912627388416 }, { target := 154, numerator := 62476908568365406177198080 }, { target := 155, numerator := 64261963098890132067975168 }, { target := 156, numerator := 62476908568365406177198080 }, { target := 157, numerator := 55336690446266502614089728 }, { target := 158, numerator := 2590114123791377267517554688 }, { target := 159, numerator := 705096539557266726856949760 }, { target := 160, numerator := 64261963098890132067975168 }, { target := 161, numerator := 2590114123791377267517554688 }, { target := 162, numerator := 62476908568365406177198080 }, { target := 163, numerator := 62476908568365406177198080 }, { target := 164, numerator := 53551635915741776723312640 }, { target := 165, numerator := 62476908568365406177198080 }, { target := 166, numerator := 705096539557266726856949760 }, { target := 167, numerator := 53551635915741776723312640 }, { target := 168, numerator := 62476908568365406177198080 }, { target := 169, numerator := 55336690446266502614089728 }, { target := 180, numerator := 999630537093846498835169280 }, { target := 181, numerator := 1028191409582242113087602688 }, { target := 182, numerator := 999630537093846498835169280 }, { target := 183, numerator := 885387047140264041825435648 }, { target := 184, numerator := 41441825980662036280280875008 }, { target := 185, numerator := 11281544632916267629711196160 }, { target := 186, numerator := 1028191409582242113087602688 }, { target := 187, numerator := 41441825980662036280280875008 }, { target := 188, numerator := 999630537093846498835169280 }, { target := 189, numerator := 999630537093846498835169280 }, { target := 190, numerator := 856826174651868427573002240 }, { target := 191, numerator := 999630537093846498835169280 }, { target := 192, numerator := 11281544632916267629711196160 }, { target := 193, numerator := 856826174651868427573002240 }, { target := 194, numerator := 999630537093846498835169280 }, { target := 195, numerator := 885387047140264041825435648 }, { target := 215, numerator := 72889726663092973873397760 }, { target := 216, numerator := 74972290282038487412637696 }, { target := 217, numerator := 72889726663092973873397760 }, { target := 218, numerator := 64559472187310919716438016 }, { target := 219, numerator := 3021799811089940145437147136 }, { target := 220, numerator := 822612629483477847999774720 }, { target := 221, numerator := 74972290282038487412637696 }, { target := 222, numerator := 3021799811089940145437147136 }, { target := 223, numerator := 72889726663092973873397760 }, { target := 224, numerator := 72889726663092973873397760 }, { target := 225, numerator := 62476908568365406177198080 }, { target := 226, numerator := 72889726663092973873397760 }, { target := 227, numerator := 822612629483477847999774720 }, { target := 228, numerator := 62476908568365406177198080 }, { target := 229, numerator := 72889726663092973873397760 }, { target := 230, numerator := 64559472187310919716438016 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk13

namespace RouteChunk14

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot16.Left6.expected,
    Slot16.Left7.expected,
    Slot16.Left8.expected,
    Slot16.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 295, numerator := 1895132893240417320708341760 }, { target := 296, numerator := 1949279547333000672728580096 }, { target := 297, numerator := 1895132893240417320708341760 }, { target := 298, numerator := 1678546276870083912627388416 }, { target := 299, numerator := 78566795088338443781365825536 }, { target := 300, numerator := 21387928366570424047994142720 }, { target := 301, numerator := 1949279547333000672728580096 }, { target := 302, numerator := 78566795088338443781365825536 }, { target := 303, numerator := 1895132893240417320708341760 }, { target := 304, numerator := 1895132893240417320708341760 }, { target := 305, numerator := 1624399622777500560607150080 }, { target := 306, numerator := 1895132893240417320708341760 }, { target := 307, numerator := 21387928366570424047994142720 }, { target := 308, numerator := 1624399622777500560607150080 }, { target := 309, numerator := 1895132893240417320708341760 }, { target := 310, numerator := 1678546276870083912627388416 }, { target := 321, numerator := 1895132893240417320708341760 }, { target := 322, numerator := 1949279547333000672728580096 }, { target := 323, numerator := 1895132893240417320708341760 }, { target := 324, numerator := 1678546276870083912627388416 }, { target := 325, numerator := 78566795088338443781365825536 }, { target := 326, numerator := 21387928366570424047994142720 }, { target := 327, numerator := 1949279547333000672728580096 }, { target := 328, numerator := 78566795088338443781365825536 }, { target := 329, numerator := 1895132893240417320708341760 }, { target := 330, numerator := 1895132893240417320708341760 }, { target := 331, numerator := 1624399622777500560607150080 }, { target := 332, numerator := 1895132893240417320708341760 }, { target := 333, numerator := 21387928366570424047994142720 }, { target := 334, numerator := 1624399622777500560607150080 }, { target := 335, numerator := 1895132893240417320708341760 }, { target := 336, numerator := 1678546276870083912627388416 }, { target := 370, numerator := 999630537093846498835169280 }, { target := 371, numerator := 1028191409582242113087602688 }, { target := 372, numerator := 999630537093846498835169280 }, { target := 373, numerator := 885387047140264041825435648 }, { target := 374, numerator := 41441825980662036280280875008 }, { target := 375, numerator := 11281544632916267629711196160 }, { target := 376, numerator := 1028191409582242113087602688 }, { target := 377, numerator := 41441825980662036280280875008 }, { target := 378, numerator := 999630537093846498835169280 }, { target := 379, numerator := 999630537093846498835169280 }, { target := 380, numerator := 856826174651868427573002240 }, { target := 381, numerator := 999630537093846498835169280 }, { target := 382, numerator := 11281544632916267629711196160 }, { target := 383, numerator := 856826174651868427573002240 }, { target := 384, numerator := 999630537093846498835169280 }, { target := 385, numerator := 885387047140264041825435648 }, { target := 396, numerator := 23387189440758117045664481280 }, { target := 397, numerator := 24055394853351206104112037888 }, { target := 398, numerator := 23387189440758117045664481280 }, { target := 399, numerator := 20714367790385760811874254848 }, { target := 400, numerator := 969566053672572223807404638208 }, { target := 401, numerator := 263941137974270178086784860160 }, { target := 402, numerator := 24055394853351206104112037888 }, { target := 403, numerator := 969566053672572223807404638208 }, { target := 404, numerator := 23387189440758117045664481280 }, { target := 405, numerator := 23387189440758117045664481280 }, { target := 406, numerator := 20046162377792671753426698240 }, { target := 407, numerator := 23387189440758117045664481280 }, { target := 408, numerator := 263941137974270178086784860160 }, { target := 409, numerator := 20046162377792671753426698240 }, { target := 410, numerator := 23387189440758117045664481280 }, { target := 411, numerator := 20714367790385760811874254848 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk14

namespace RouteChunk15

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot16.Left10.expected,
    Slot16.Left11.expected,
    Slot16.Left12.expected,
    Slot16.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 431, numerator := 1874307257050962185315942400 }, { target := 432, numerator := 1927858892966703962039255040 }, { target := 433, numerator := 1874307257050962185315942400 }, { target := 434, numerator := 1660100713387995078422691840 }, { target := 435, numerator := 77703423713741318025526640640 }, { target := 436, numerator := 21152896186718001805708492800 }, { target := 437, numerator := 1927858892966703962039255040 }, { target := 438, numerator := 77703423713741318025526640640 }, { target := 439, numerator := 1874307257050962185315942400 }, { target := 440, numerator := 1874307257050962185315942400 }, { target := 441, numerator := 1606549077472253301699379200 }, { target := 442, numerator := 1874307257050962185315942400 }, { target := 443, numerator := 21152896186718001805708492800 }, { target := 444, numerator := 1606549077472253301699379200 }, { target := 445, numerator := 1874307257050962185315942400 }, { target := 446, numerator := 1660100713387995078422691840 }, { target := 492, numerator := 874676719957115686480773120 }, { target := 493, numerator := 899667483384461848951652352 }, { target := 494, numerator := 874676719957115686480773120 }, { target := 495, numerator := 774713666247731036597256192 }, { target := 496, numerator := 36261597733079281745245765632 }, { target := 497, numerator := 9871351553801734175997296640 }, { target := 498, numerator := 899667483384461848951652352 }, { target := 499, numerator := 36261597733079281745245765632 }, { target := 500, numerator := 874676719957115686480773120 }, { target := 501, numerator := 874676719957115686480773120 }, { target := 502, numerator := 749722902820384874126376960 }, { target := 503, numerator := 874676719957115686480773120 }, { target := 504, numerator := 9871351553801734175997296640 }, { target := 505, numerator := 749722902820384874126376960 }, { target := 506, numerator := 874676719957115686480773120 }, { target := 507, numerator := 774713666247731036597256192 }, { target := 527, numerator := 1895132893240417320708341760 }, { target := 528, numerator := 1949279547333000672728580096 }, { target := 529, numerator := 1895132893240417320708341760 }, { target := 530, numerator := 1678546276870083912627388416 }, { target := 531, numerator := 78566795088338443781365825536 }, { target := 532, numerator := 21387928366570424047994142720 }, { target := 533, numerator := 1949279547333000672728580096 }, { target := 534, numerator := 78566795088338443781365825536 }, { target := 535, numerator := 1895132893240417320708341760 }, { target := 536, numerator := 1895132893240417320708341760 }, { target := 537, numerator := 1624399622777500560607150080 }, { target := 538, numerator := 1895132893240417320708341760 }, { target := 539, numerator := 21387928366570424047994142720 }, { target := 540, numerator := 1624399622777500560607150080 }, { target := 541, numerator := 1895132893240417320708341760 }, { target := 542, numerator := 1678546276870083912627388416 }, { target := 637, numerator := 72889726663092973873397760 }, { target := 638, numerator := 74972290282038487412637696 }, { target := 639, numerator := 72889726663092973873397760 }, { target := 640, numerator := 64559472187310919716438016 }, { target := 641, numerator := 3021799811089940145437147136 }, { target := 642, numerator := 822612629483477847999774720 }, { target := 643, numerator := 74972290282038487412637696 }, { target := 644, numerator := 3021799811089940145437147136 }, { target := 645, numerator := 72889726663092973873397760 }, { target := 646, numerator := 72889726663092973873397760 }, { target := 647, numerator := 62476908568365406177198080 }, { target := 648, numerator := 72889726663092973873397760 }, { target := 649, numerator := 822612629483477847999774720 }, { target := 650, numerator := 62476908568365406177198080 }, { target := 651, numerator := 72889726663092973873397760 }, { target := 652, numerator := 64559472187310919716438016 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk15

namespace RouteChunk16

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot16.Left14.expected,
    Slot16.Left15.expected,
    Slot16.Left16.expected,
    Slot16.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 663, numerator := 1874307257050962185315942400 }, { target := 664, numerator := 1927858892966703962039255040 }, { target := 665, numerator := 1874307257050962185315942400 }, { target := 666, numerator := 1660100713387995078422691840 }, { target := 667, numerator := 77703423713741318025526640640 }, { target := 668, numerator := 21152896186718001805708492800 }, { target := 669, numerator := 1927858892966703962039255040 }, { target := 670, numerator := 77703423713741318025526640640 }, { target := 671, numerator := 1874307257050962185315942400 }, { target := 672, numerator := 1874307257050962185315942400 }, { target := 673, numerator := 1606549077472253301699379200 }, { target := 674, numerator := 1874307257050962185315942400 }, { target := 675, numerator := 21152896186718001805708492800 }, { target := 676, numerator := 1606549077472253301699379200 }, { target := 677, numerator := 1874307257050962185315942400 }, { target := 678, numerator := 1660100713387995078422691840 }, { target := 698, numerator := 72889726663092973873397760 }, { target := 699, numerator := 74972290282038487412637696 }, { target := 700, numerator := 72889726663092973873397760 }, { target := 701, numerator := 64559472187310919716438016 }, { target := 702, numerator := 3021799811089940145437147136 }, { target := 703, numerator := 822612629483477847999774720 }, { target := 704, numerator := 74972290282038487412637696 }, { target := 705, numerator := 3021799811089940145437147136 }, { target := 706, numerator := 72889726663092973873397760 }, { target := 707, numerator := 72889726663092973873397760 }, { target := 708, numerator := 62476908568365406177198080 }, { target := 709, numerator := 72889726663092973873397760 }, { target := 710, numerator := 822612629483477847999774720 }, { target := 711, numerator := 62476908568365406177198080 }, { target := 712, numerator := 72889726663092973873397760 }, { target := 713, numerator := 64559472187310919716438016 }, { target := 759, numerator := 1895132893240417320708341760 }, { target := 760, numerator := 1949279547333000672728580096 }, { target := 761, numerator := 1895132893240417320708341760 }, { target := 762, numerator := 1678546276870083912627388416 }, { target := 763, numerator := 78566795088338443781365825536 }, { target := 764, numerator := 21387928366570424047994142720 }, { target := 765, numerator := 1949279547333000672728580096 }, { target := 766, numerator := 78566795088338443781365825536 }, { target := 767, numerator := 1895132893240417320708341760 }, { target := 768, numerator := 1895132893240417320708341760 }, { target := 769, numerator := 1624399622777500560607150080 }, { target := 770, numerator := 1895132893240417320708341760 }, { target := 771, numerator := 21387928366570424047994142720 }, { target := 772, numerator := 1624399622777500560607150080 }, { target := 773, numerator := 1895132893240417320708341760 }, { target := 774, numerator := 1678546276870083912627388416 }, { target := 794, numerator := 1895132893240417320708341760 }, { target := 795, numerator := 1949279547333000672728580096 }, { target := 796, numerator := 1895132893240417320708341760 }, { target := 797, numerator := 1678546276870083912627388416 }, { target := 798, numerator := 78566795088338443781365825536 }, { target := 799, numerator := 21387928366570424047994142720 }, { target := 800, numerator := 1949279547333000672728580096 }, { target := 801, numerator := 78566795088338443781365825536 }, { target := 802, numerator := 1895132893240417320708341760 }, { target := 803, numerator := 1895132893240417320708341760 }, { target := 804, numerator := 1624399622777500560607150080 }, { target := 805, numerator := 1895132893240417320708341760 }, { target := 806, numerator := 21387928366570424047994142720 }, { target := 807, numerator := 1624399622777500560607150080 }, { target := 808, numerator := 1895132893240417320708341760 }, { target := 809, numerator := 1678546276870083912627388416 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk16

namespace RouteChunk17

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot16.Left18.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 29371678002633553196278087680 }, { target := 2, numerator := 26846262697734219650429878272 }, { target := 3, numerator := 29371678002633553196278087680 }, { target := 4, numerator := 26846262697734219650429878272 }, { target := 10, numerator := 197616741081437527290675200 }, { target := 11, numerator := 3960239491272008046905131008 }, { target := 12, numerator := 6647827169979558418058313728 }, { target := 13, numerator := 6379068402108803380942995456 }, { target := 14, numerator := 197616741081437527290675200 }, { target := 15, numerator := 6379068402108803380942995456 }, { target := 16, numerator := 4260616937715793088386957312 }, { target := 17, numerator := 205521410724695028382302208 }, { target := 18, numerator := 3960239491272008046905131008 }, { target := 19, numerator := 189712071438180026199048192 }, { target := 51, numerator := 106831124249152505375201689600 }, { target := 52, numerator := 97645644407169299305558179840 }, { target := 53, numerator := 106831124249152505375201689600 }, { target := 54, numerator := 97645644407169299305558179840 }, { target := 55, numerator := 7297723340529263355887616000 }, { target := 56, numerator := 146246375744206437651987824640 }, { target := 57, numerator := 245495413175404419292059402240 }, { target := 58, numerator := 235570509432284621128052244480 }, { target := 59, numerator := 7297723340529263355887616000 }, { target := 60, numerator := 235570509432284621128052244480 }, { target := 61, numerator := 157338915221810917952937000960 }, { target := 62, numerator := 7589632274150433890123120640 }, { target := 63, numerator := 146246375744206437651987824640 }, { target := 64, numerator := 7005814406908092821652111360 }, { target := 144, numerator := 7297721553500931215274803200 }, { target := 145, numerator := 146246339932158661554107056128 }, { target := 146, numerator := 245495353059771326081844379648 }, { target := 147, numerator := 235570451747010059629070647296 }, { target := 148, numerator := 7297721553500931215274803200 }, { target := 149, numerator := 235570451747010059629070647296 }, { target := 150, numerator := 157338876693480077001324756992 }, { target := 151, numerator := 7589630415640968463885795328 }, { target := 152, numerator := 146246339932158661554107056128 }, { target := 153, numerator := 7005812691360893966663811072 }, { target := 482, numerator := 197618528109769667903488000 }, { target := 483, numerator := 3960275303319784144785899520 }, { target := 484, numerator := 6647887285612651628273336320 }, { target := 485, numerator := 6379126087383364879924592640 }, { target := 486, numerator := 197618528109769667903488000 }, { target := 487, numerator := 6379126087383364879924592640 }, { target := 488, numerator := 4260655466046634039999201280 }, { target := 489, numerator := 205523269234160454619627520 }, { target := 490, numerator := 3960275303319784144785899520 }, { target := 491, numerator := 189713786985378881187348480 }, { target := 890, numerator := 62476908568365406177198080 }, { target := 891, numerator := 64261963098890132067975168 }, { target := 892, numerator := 62476908568365406177198080 }, { target := 893, numerator := 55336690446266502614089728 }, { target := 894, numerator := 2590114123791377267517554688 }, { target := 895, numerator := 705096539557266726856949760 }, { target := 896, numerator := 64261963098890132067975168 }, { target := 897, numerator := 2590114123791377267517554688 }, { target := 898, numerator := 62476908568365406177198080 }, { target := 899, numerator := 62476908568365406177198080 }, { target := 900, numerator := 53551635915741776723312640 }, { target := 901, numerator := 62476908568365406177198080 }, { target := 902, numerator := 705096539557266726856949760 }, { target := 903, numerator := 53551635915741776723312640 }, { target := 904, numerator := 62476908568365406177198080 }, { target := 905, numerator := 55336690446266502614089728 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk17

namespace RouteChunk18

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 118842272105595403608187207680 }, { target := 50, numerator := 118842215437197609172444643328 }, { target := 140, numerator := 29371678002633553196278087680 }, { target := 141, numerator := 26846262697734219650429878272 }, { target := 142, numerator := 29371678002633553196278087680 }, { target := 143, numerator := 26846262697734219650429878272 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk18

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent3
