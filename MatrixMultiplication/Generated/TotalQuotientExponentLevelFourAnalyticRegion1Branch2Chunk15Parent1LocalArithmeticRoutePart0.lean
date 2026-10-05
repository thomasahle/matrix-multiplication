import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 63; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected,
    Slot1.Left6.expected,
    Slot1.Left7.expected,
    Slot1.Left8.expected,
    Slot1.Left9.expected,
    Slot1.Left10.expected,
    Slot1.Left11.expected,
    Slot1.Left12.expected,
    Slot1.Left13.expected,
    Slot1.Left14.expected,
    Slot1.Left15.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 5950181768415752969256960 }, { target := 132, numerator := 105913235477800402852773888 }, { target := 133, numerator := 5950181768415752969256960 }, { target := 134, numerator := 94211211333249422013235200 }, { target := 135, numerator := 160853247139505855268913152 }, { target := 136, numerator := 5950181768415752969256960 }, { target := 137, numerator := 160853247139505855268913152 }, { target := 138, numerator := 160853247139505855268913152 }, { target := 139, numerator := 105913235477800402852773888 }, { target := 140, numerator := 5950181768415752969256960 }, { target := 227, numerator := 158671513824420079180185600 }, { target := 228, numerator := 2824352946074677409407303680 }, { target := 229, numerator := 158671513824420079180185600 }, { target := 230, numerator := 2512298968886651253686272000 }, { target := 231, numerator := 4289419923720156140504350720 }, { target := 232, numerator := 158671513824420079180185600 }, { target := 233, numerator := 4289419923720156140504350720 }, { target := 234, numerator := 4289419923720156140504350720 }, { target := 235, numerator := 2824352946074677409407303680 }, { target := 236, numerator := 158671513824420079180185600 }, { target := 253, numerator := 151729635094601700716052480 }, { target := 254, numerator := 2700787504683910272745734144 }, { target := 255, numerator := 151729635094601700716052480 }, { target := 256, numerator := 2402385888997860261337497600 }, { target := 257, numerator := 4101757802057399309357285376 }, { target := 258, numerator := 151729635094601700716052480 }, { target := 259, numerator := 4101757802057399309357285376 }, { target := 260, numerator := 4101757802057399309357285376 }, { target := 261, numerator := 2700787504683910272745734144 }, { target := 262, numerator := 151729635094601700716052480 }, { target := 263, numerator := 1353996917968384675670917120 }, { target := 265, numerator := 1353996917968384675670917120 }, { target := 338, numerator := 1392682544196052809261514752 }, { target := 340, numerator := 1392682544196052809261514752 }, { target := 352, numerator := 1353996917968384675670917120 }, { target := 354, numerator := 1353996917968384675670917120 }, { target := 479, numerator := 1199254413057712141308526592 }, { target := 481, numerator := 1199254413057712141308526592 }, { target := 554, numerator := 56132843656346461839957164032 }, { target := 556, numerator := 56132843656346461839957164032 }, { target := 568, numerator := 15280822359928912768286064640 }, { target := 570, numerator := 15280822359928912768286064640 }, { target := 599, numerator := 1392682544196052809261514752 }, { target := 601, numerator := 1392682544196052809261514752 }, { target := 613, numerator := 56132843656346461839957164032 }, { target := 615, numerator := 56132843656346461839957164032 }, { target := 618, numerator := 1353996917968384675670917120 }, { target := 620, numerator := 1353996917968384675670917120 }, { target := 694, numerator := 1353996917968384675670917120 }, { target := 696, numerator := 1353996917968384675670917120 }, { target := 708, numerator := 1160568786830044007717928960 }, { target := 710, numerator := 1160568786830044007717928960 }, { target := 739, numerator := 1353996917968384675670917120 }, { target := 741, numerator := 1353996917968384675670917120 }, { target := 753, numerator := 15280822359928912768286064640 }, { target := 755, numerator := 15280822359928912768286064640 }, { target := 758, numerator := 1160568786830044007717928960 }, { target := 760, numerator := 1160568786830044007717928960 }, { target := 773, numerator := 1353996917968384675670917120 }, { target := 775, numerator := 1353996917968384675670917120 }, { target := 778, numerator := 1199254413057712141308526592 }, { target := 780, numerator := 1199254413057712141308526592 }]

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
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 302, numerator := 4958484807013127474380800 }, { target := 303, numerator := 88261029564833669043978240 }, { target := 304, numerator := 4958484807013127474380800 }, { target := 305, numerator := 78509342777707851677696000 }, { target := 306, numerator := 134044372616254879390760960 }, { target := 307, numerator := 4958484807013127474380800 }, { target := 308, numerator := 134044372616254879390760960 }, { target := 309, numerator := 134044372616254879390760960 }, { target := 310, numerator := 88261029564833669043978240 }, { target := 311, numerator := 4958484807013127474380800 }, { target := 328, numerator := 155696422940212202695557120 }, { target := 329, numerator := 2771396328335777207980916736 }, { target := 330, numerator := 155696422940212202695557120 }, { target := 331, numerator := 2465193363220026542679654400 }, { target := 332, numerator := 4208993300150403212869894144 }, { target := 333, numerator := 155696422940212202695557120 }, { target := 334, numerator := 4208993300150403212869894144 }, { target := 335, numerator := 4208993300150403212869894144 }, { target := 336, numerator := 2771396328335777207980916736 }, { target := 337, numerator := 155696422940212202695557120 }, { target := 342, numerator := 4958484807013127474380800 }, { target := 343, numerator := 88261029564833669043978240 }, { target := 344, numerator := 4958484807013127474380800 }, { target := 345, numerator := 78509342777707851677696000 }, { target := 346, numerator := 134044372616254879390760960 }, { target := 347, numerator := 4958484807013127474380800 }, { target := 348, numerator := 134044372616254879390760960 }, { target := 349, numerator := 134044372616254879390760960 }, { target := 350, numerator := 88261029564833669043978240 }, { target := 351, numerator := 4958484807013127474380800 }, { target := 443, numerator := 151729635094601700716052480 }, { target := 444, numerator := 2700787504683910272745734144 }, { target := 445, numerator := 151729635094601700716052480 }, { target := 446, numerator := 2402385888997860261337497600 }, { target := 447, numerator := 4101757802057399309357285376 }, { target := 448, numerator := 151729635094601700716052480 }, { target := 449, numerator := 4101757802057399309357285376 }, { target := 450, numerator := 4101757802057399309357285376 }, { target := 451, numerator := 2700787504683910272745734144 }, { target := 452, numerator := 151729635094601700716052480 }, { target := 469, numerator := 86277635642028418054225920 }, { target := 470, numerator := 1535741914428105841365221376 }, { target := 471, numerator := 86277635642028418054225920 }, { target := 472, numerator := 1366062564332116619191910400 }, { target := 473, numerator := 2332372083522834901399240704 }, { target := 474, numerator := 86277635642028418054225920 }, { target := 475, numerator := 2332372083522834901399240704 }, { target := 476, numerator := 2332372083522834901399240704 }, { target := 477, numerator := 1535741914428105841365221376 }, { target := 478, numerator := 86277635642028418054225920 }, { target := 518, numerator := 155696422940212202695557120 }, { target := 519, numerator := 2771396328335777207980916736 }, { target := 520, numerator := 155696422940212202695557120 }, { target := 521, numerator := 2465193363220026542679654400 }, { target := 522, numerator := 4208993300150403212869894144 }, { target := 523, numerator := 155696422940212202695557120 }, { target := 524, numerator := 4208993300150403212869894144 }, { target := 525, numerator := 4208993300150403212869894144 }, { target := 526, numerator := 2771396328335777207980916736 }, { target := 527, numerator := 155696422940212202695557120 }]

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
    Slot2.Left9.expected,
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 544, numerator := 2430649252397835087941468160 }, { target := 545, numerator := 43265556692681464565358133248 }, { target := 546, numerator := 2430649252397835087941468160 }, { target := 547, numerator := 38485279829632388892406579200 }, { target := 548, numerator := 65708551456488141877351022592 }, { target := 549, numerator := 2430649252397835087941468160 }, { target := 550, numerator := 65708551456488141877351022592 }, { target := 551, numerator := 65708551456488141877351022592 }, { target := 552, numerator := 43265556692681464565358133248 }, { target := 553, numerator := 2430649252397835087941468160 }, { target := 558, numerator := 95202908294652047508111360 }, { target := 559, numerator := 1694611767644806445644382208 }, { target := 560, numerator := 95202908294652047508111360 }, { target := 561, numerator := 1507379381331990752211763200 }, { target := 562, numerator := 2573651954232093684302610432 }, { target := 563, numerator := 95202908294652047508111360 }, { target := 564, numerator := 2573651954232093684302610432 }, { target := 565, numerator := 2573651954232093684302610432 }, { target := 566, numerator := 1694611767644806445644382208 }, { target := 567, numerator := 95202908294652047508111360 }, { target := 589, numerator := 158671513824420079180185600 }, { target := 590, numerator := 2824352946074677409407303680 }, { target := 591, numerator := 158671513824420079180185600 }, { target := 592, numerator := 2512298968886651253686272000 }, { target := 593, numerator := 4289419923720156140504350720 }, { target := 594, numerator := 158671513824420079180185600 }, { target := 595, numerator := 4289419923720156140504350720 }, { target := 596, numerator := 4289419923720156140504350720 }, { target := 597, numerator := 2824352946074677409407303680 }, { target := 598, numerator := 158671513824420079180185600 }, { target := 603, numerator := 151729635094601700716052480 }, { target := 604, numerator := 2700787504683910272745734144 }, { target := 605, numerator := 151729635094601700716052480 }, { target := 606, numerator := 2402385888997860261337497600 }, { target := 607, numerator := 4101757802057399309357285376 }, { target := 608, numerator := 151729635094601700716052480 }, { target := 609, numerator := 4101757802057399309357285376 }, { target := 610, numerator := 4101757802057399309357285376 }, { target := 611, numerator := 2700787504683910272745734144 }, { target := 612, numerator := 151729635094601700716052480 }, { target := 658, numerator := 4958484807013127474380800 }, { target := 659, numerator := 88261029564833669043978240 }, { target := 660, numerator := 4958484807013127474380800 }, { target := 661, numerator := 78509342777707851677696000 }, { target := 662, numerator := 134044372616254879390760960 }, { target := 663, numerator := 4958484807013127474380800 }, { target := 664, numerator := 134044372616254879390760960 }, { target := 665, numerator := 134044372616254879390760960 }, { target := 666, numerator := 88261029564833669043978240 }, { target := 667, numerator := 4958484807013127474380800 }, { target := 684, numerator := 95202908294652047508111360 }, { target := 685, numerator := 1694611767644806445644382208 }, { target := 686, numerator := 95202908294652047508111360 }, { target := 687, numerator := 1507379381331990752211763200 }, { target := 688, numerator := 2573651954232093684302610432 }, { target := 689, numerator := 95202908294652047508111360 }, { target := 690, numerator := 2573651954232093684302610432 }, { target := 691, numerator := 2573651954232093684302610432 }, { target := 692, numerator := 1694611767644806445644382208 }, { target := 693, numerator := 95202908294652047508111360 }]

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
    Slot2.Left15.expected,
    Slot2.Left16.expected,
    Slot2.Left17.expected,
    Slot2.Left18.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot3.Left7.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left6.expected,
    Slot4.Left14.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 7018641103477793763782295552 }, { target := 134, numerator := 25108725140044748123510145024 }, { target := 136, numerator := 7018638770194070545543200768 }, { target := 227, numerator := 735891861109157719542205513728 }, { target := 230, numerator := 2632604545662004405009001742336 }, { target := 232, numerator := 735891616468567573970395594752 }, { target := 263, numerator := 29688656245918335748255252480 }, { target := 265, numerator := 29688656245918335748255252480 }, { target := 302, numerator := 7932178739706872754931236864000 }, { target := 305, numerator := 28376845717088683337258631168000 }, { target := 307, numerator := 7932176102725828967846117376000 }, { target := 338, numerator := 2485805503581974382846765170688 }, { target := 340, numerator := 2485805503581974382846765170688 }, { target := 356, numerator := 20339123827290455933548756992 }, { target := 589, numerator := 735892422465720422716944678912 }, { target := 592, numerator := 2632606553878043759143859257344 }, { target := 594, numerator := 735892177824943659235575595008 }, { target := 599, numerator := 2485806403192789369514178379776 }, { target := 601, numerator := 2485806403192789369514178379776 }, { target := 617, numerator := 197006239888212100913534337024 }, { target := 698, numerator := 4958484807013127474380800 }, { target := 699, numerator := 88261029564833669043978240 }, { target := 700, numerator := 4958484807013127474380800 }, { target := 701, numerator := 78509342777707851677696000 }, { target := 702, numerator := 134044372616254879390760960 }, { target := 703, numerator := 4958484807013127474380800 }, { target := 704, numerator := 134044372616254879390760960 }, { target := 705, numerator := 134044372616254879390760960 }, { target := 706, numerator := 88261029564833669043978240 }, { target := 707, numerator := 4958484807013127474380800 }, { target := 729, numerator := 152721332056004326210928640 }, { target := 730, numerator := 2718439710596877006554529792 }, { target := 731, numerator := 152721332056004326210928640 }, { target := 732, numerator := 2418087757553401831673036800 }, { target := 733, numerator := 4128566676580650285235437568 }, { target := 734, numerator := 152721332056004326210928640 }, { target := 735, numerator := 4128566676580650285235437568 }, { target := 736, numerator := 4128566676580650285235437568 }, { target := 737, numerator := 2718439710596877006554529792 }, { target := 738, numerator := 152721332056004326210928640 }, { target := 743, numerator := 86277635642028418054225920 }, { target := 744, numerator := 1535741914428105841365221376 }, { target := 745, numerator := 86277635642028418054225920 }, { target := 746, numerator := 1366062564332116619191910400 }, { target := 747, numerator := 2332372083522834901399240704 }, { target := 748, numerator := 86277635642028418054225920 }, { target := 749, numerator := 2332372083522834901399240704 }, { target := 750, numerator := 2332372083522834901399240704 }, { target := 751, numerator := 1535741914428105841365221376 }, { target := 752, numerator := 86277635642028418054225920 }, { target := 763, numerator := 5950181768415752969256960 }, { target := 764, numerator := 105913235477800402852773888 }, { target := 765, numerator := 5950181768415752969256960 }, { target := 766, numerator := 94211211333249422013235200 }, { target := 767, numerator := 160853247139505855268913152 }, { target := 768, numerator := 5950181768415752969256960 }, { target := 769, numerator := 160853247139505855268913152 }, { target := 770, numerator := 160853247139505855268913152 }, { target := 771, numerator := 105913235477800402852773888 }, { target := 772, numerator := 5950181768415752969256960 }, { target := 773, numerator := 29687756635103349080842043392 }, { target := 775, numerator := 29687756635103349080842043392 }, { target := 777, numerator := 20339123827290455933548756992 }]

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
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 3215427683573110940415033344 }, { target := 81, numerator := 3818320374243069241742852096 }, { target := 82, numerator := 2913981338238131789751123968 }, { target := 83, numerator := 30044152418386255349502967808 }, { target := 84, numerator := 3617356144019749807966912512 }, { target := 85, numerator := 2913981338238131789751123968 }, { target := 86, numerator := 3617356144019749807966912512 }, { target := 87, numerator := 3617356144019749807966912512 }, { target := 88, numerator := 154943421502179283441249419264 }, { target := 89, numerator := 3617356144019749807966912512 }, { target := 90, numerator := 30044152418386255349502967808 }, { target := 91, numerator := 154943421502179283441249419264 }, { target := 92, numerator := 3215427683573110940415033344 }, { target := 93, numerator := 3617356144019749807966912512 }, { target := 94, numerator := 3617356144019749807966912512 }, { target := 95, numerator := 3818320374243069241742852096 }, { target := 176, numerator := 112531952191445377627908472832 }, { target := 177, numerator := 133631693227341385933141311488 }, { target := 178, numerator := 101982081673497373475292053504 }, { target := 179, numerator := 1051470428288817747210769793024 }, { target := 180, numerator := 126598446215376049831397031936 }, { target := 181, numerator := 101982081673497373475292053504 }, { target := 182, numerator := 126598446215376049831397031936 }, { target := 183, numerator := 126598446215376049831397031936 }, { target := 184, numerator := 5422633446225274134444839534592 }, { target := 185, numerator := 126598446215376049831397031936 }, { target := 186, numerator := 1051470428288817747210769793024 }, { target := 187, numerator := 5422633446225274134444839534592 }, { target := 188, numerator := 112531952191445377627908472832 }, { target := 189, numerator := 126598446215376049831397031936 }, { target := 190, numerator := 126598446215376049831397031936 }, { target := 191, numerator := 133631693227341385933141311488 }, { target := 286, numerator := 112532007384103646166886907904 }, { target := 287, numerator := 133631758768623079823178203136 }, { target := 288, numerator := 101982131691843929338741260288 }, { target := 289, numerator := 1051470943995218443871849545728 }, { target := 290, numerator := 126598508307116601937747771392 }, { target := 291, numerator := 101982131691843929338741260288 }, { target := 292, numerator := 126598508307116601937747771392 }, { target := 293, numerator := 126598508307116601937747771392 }, { target := 294, numerator := 5422636105821494449666862874624 }, { target := 295, numerator := 126598508307116601937747771392 }, { target := 296, numerator := 1051470943995218443871849545728 }, { target := 297, numerator := 5422636105821494449666862874624 }, { target := 298, numerator := 112532007384103646166886907904 }, { target := 299, numerator := 126598508307116601937747771392 }, { target := 300, numerator := 126598508307116601937747771392 }, { target := 301, numerator := 133631758768623079823178203136 }, { target := 763, numerator := 7018641103477793763782295552 }, { target := 766, numerator := 25108725140044748123510145024 }, { target := 768, numerator := 7018638770194070545543200768 }]

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
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected,
    Slot7.Left4.expected,
    Slot7.Left5.expected,
    Slot7.Left6.expected,
    Slot7.Left7.expected,
    Slot7.Left8.expected,
    Slot7.Left9.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 80715926397667565121713471488 }, { target := 82, numerator := 2980731778093422095771935703040 }, { target := 85, numerator := 2980731048187410397266138103808 }, { target := 92, numerator := 80716656303679263627511070720 }, { target := 131, numerator := 48503916194946056671375392768 }, { target := 134, numerator := 176419198696382046999108648960 }, { target := 136, numerator := 48503916194946056671375392768 }, { target := 176, numerator := 2925171889717709242246465847296 }, { target := 178, numerator := 108022706263817582893969629511680 }, { target := 181, numerator := 108022679811782119194797577076736 }, { target := 188, numerator := 2925198341753172941418518282240 }, { target := 227, numerator := 7163774591558441873897410265088 }, { target := 230, numerator := 26056192411447561004145558159360 }, { target := 232, numerator := 7163774591558441873897410265088 }, { target := 263, numerator := 111268680605679059106822881280 }, { target := 265, numerator := 111268627548650251865070501888 }, { target := 286, numerator := 2925172964706962327636845527040 }, { target := 288, numerator := 108022745961740542905096024883200 }, { target := 291, numerator := 108022719509695358186128293232640 }, { target := 298, numerator := 2925199416752147046604577177600 }, { target := 302, numerator := 74666824509401052157682877726720 }, { target := 305, numerator := 271579335907818093865544869478400 }, { target := 307, numerator := 74666824509401052157682877726720 }, { target := 338, numerator := 9356498997140088095012091330560 }, { target := 340, numerator := 9356494535614759278873019416576 }, { target := 356, numerator := 3597763239173136423925579776 }, { target := 572, numerator := 86114203982789265372670328832 }, { target := 573, numerator := 3215400087243976670925815808 }, { target := 574, numerator := 3818287603602222296724406272 }, { target := 575, numerator := 2913956329064853858026520576 }, { target := 576, numerator := 30043894565185907018963091456 }, { target := 577, numerator := 3617325098149473754791542784 }, { target := 578, numerator := 2913956329064853858026520576 }, { target := 579, numerator := 3617325098149473754791542784 }, { target := 580, numerator := 3617325098149473754791542784 }, { target := 581, numerator := 154942091704069125830237749248 }, { target := 582, numerator := 3617325098149473754791542784 }, { target := 583, numerator := 30043894565185907018963091456 }, { target := 584, numerator := 154942091704069125830237749248 }, { target := 585, numerator := 3215400087243976670925815808 }, { target := 586, numerator := 3617325098149473754791542784 }, { target := 587, numerator := 3617325098149473754791542784 }, { target := 588, numerator := 3818287603602222296724406272 }, { target := 589, numerator := 7163774591558441873897410265088 }, { target := 592, numerator := 26056192411447561004145558159360 }, { target := 594, numerator := 7163774591558441873897410265088 }, { target := 599, numerator := 9356496739848371103166208409600 }, { target := 601, numerator := 9356492278324118647338078044160 }, { target := 617, numerator := 64411567669067442428345057280 }, { target := 622, numerator := 74740629871854834097034625024 }, { target := 712, numerator := 3597763239173136423925579776 }, { target := 757, numerator := 74624572993171829696262832128 }, { target := 762, numerator := 74972743629220842898578210816 }, { target := 763, numerator := 48503916194946056671375392768 }, { target := 766, numerator := 176419198696382046999108648960 }, { target := 768, numerator := 48503916194946056671375392768 }, { target := 773, numerator := 111270937897396050952705802240 }, { target := 775, numerator := 111270884839290883400011874304 }, { target := 777, numerator := 3597763239173136423925579776 }, { target := 782, numerator := 86114203982789265372670328832 }, { target := 783, numerator := 3597763239173136423925579776 }]

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
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 14139981904717099283282657280 }, { target := 27, numerator := 237551695999247267959148642304 }, { target := 28, numerator := 514695341331702413911488724992 }, { target := 29, numerator := 16967978285660519139939188736 }, { target := 30, numerator := 271487652570568306239027019776 }, { target := 31, numerator := 19795974666603938996595720192 }, { target := 32, numerator := 514695341331702413911488724992 }, { target := 33, numerator := 514695341331702413911488724992 }, { target := 34, numerator := 271487652570568306239027019776 }, { target := 35, numerator := 6351679871598920998050569650176 }, { target := 36, numerator := 509039348569815574198175662080 }, { target := 37, numerator := 237551695999247267959148642304 }, { target := 38, numerator := 514695341331702413911488724992 }, { target := 39, numerator := 19795974666603938996595720192 }, { target := 40, numerator := 509039348569815574198175662080 }, { target := 41, numerator := 19795974666603938996595720192 }, { target := 42, numerator := 514695341331702413911488724992 }, { target := 43, numerator := 514695341331702413911488724992 }, { target := 44, numerator := 16967978285660519139939188736 }, { target := 157, numerator := 47930719859072024606912020480 }, { target := 158, numerator := 805236093632410013396121944064 }, { target := 159, numerator := 1744678202870221695691597545472 }, { target := 160, numerator := 57516863830886429528294424576 }, { target := 161, numerator := 920269821294182872452710793216 }, { target := 162, numerator := 67103007802700834449676828672 }, { target := 163, numerator := 1744678202870221695691597545472 }, { target := 164, numerator := 1744678202870221695691597545472 }, { target := 165, numerator := 920269821294182872452710793216 }, { target := 166, numerator := 21530479360695153453424879599616 }, { target := 167, numerator := 1725505914926592885848832737280 }, { target := 168, numerator := 805236093632410013396121944064 }, { target := 169, numerator := 1744678202870221695691597545472 }, { target := 170, numerator := 67103007802700834449676828672 }, { target := 171, numerator := 1725505914926592885848832737280 }, { target := 172, numerator := 67103007802700834449676828672 }, { target := 173, numerator := 1744678202870221695691597545472 }, { target := 174, numerator := 1744678202870221695691597545472 }, { target := 175, numerator := 57516863830886429528294424576 }, { target := 263, numerator := 87913085602375833584633118720 }, { target := 265, numerator := 87913085602375833584633118720 }, { target := 267, numerator := 14139981904717099283282657280 }, { target := 268, numerator := 237551695999247267959148642304 }, { target := 269, numerator := 514695341331702413911488724992 }, { target := 270, numerator := 16967978285660519139939188736 }, { target := 271, numerator := 271487652570568306239027019776 }, { target := 272, numerator := 19795974666603938996595720192 }, { target := 273, numerator := 514695341331702413911488724992 }, { target := 274, numerator := 514695341331702413911488724992 }, { target := 275, numerator := 271487652570568306239027019776 }, { target := 276, numerator := 6351679871598920998050569650176 }, { target := 277, numerator := 509039348569815574198175662080 }, { target := 278, numerator := 237551695999247267959148642304 }, { target := 279, numerator := 514695341331702413911488724992 }, { target := 280, numerator := 19795974666603938996595720192 }, { target := 281, numerator := 509039348569815574198175662080 }, { target := 282, numerator := 19795974666603938996595720192 }, { target := 283, numerator := 514695341331702413911488724992 }, { target := 284, numerator := 514695341331702413911488724992 }, { target := 285, numerator := 16967978285660519139939188736 }, { target := 573, numerator := 80714851408414479731333791744 }, { target := 575, numerator := 2980692080170462084645540331520 }, { target := 578, numerator := 2980691350274171405935421947904 }, { target := 585, numerator := 80715581304705158441452175360 }]

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
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected,
    Slot12.Left6.expected,
    Slot12.Left7.expected,
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
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 212309140352878821504857407488 }, { target := 82, numerator := 7976999809771650345420315426816 }, { target := 85, numerator := 7976396492399903214188869189632 }, { target := 92, numerator := 212912457724625952736303644672 }, { target := 131, numerator := 33975917038592899192507596800 }, { target := 134, numerator := 116633382479992486726614384640 }, { target := 136, numerator := 33975917038592899192507596800 }, { target := 176, numerator := 7976999809771650345420315426816 }, { target := 178, numerator := 299716375184475734473114241728512 }, { target := 181, numerator := 299693707000940820827868468609024 }, { target := 188, numerator := 7999667993306563990666088546304 }, { target := 227, numerator := 5424159786936693030511024537600 }, { target := 230, numerator := 18620192130319092631055347220480 }, { target := 232, numerator := 5424159786936693030511024537600 }, { target := 286, numerator := 7976396492399903214188869189632 }, { target := 288, numerator := 299693707000940820827868468609024 }, { target := 291, numerator := 299671040531848584718199499522048 }, { target := 298, numerator := 7999062961492139323857838276608 }, { target := 302, numerator := 54124957817342723942946281881600 }, { target := 305, numerator := 185801516399188697425553056071680 }, { target := 307, numerator := 54124957817342723942946281881600 }, { target := 338, numerator := 68376844357403426121381314560 }, { target := 340, numerator := 68376844357403426121381314560 }, { target := 352, numerator := 78144964979889629853007216640 }, { target := 354, numerator := 78144964979889629853007216640 }, { target := 479, numerator := 91820333851370315077283479552 }, { target := 481, numerator := 91820333851370315077283479552 }, { target := 554, numerator := 1084261389095968614210475130880 }, { target := 556, numerator := 1084261389095968614210475130880 }, { target := 568, numerator := 2438122907372556451413825159168 }, { target := 570, numerator := 2438122907372556451413825159168 }, { target := 573, numerator := 212912457724625952736303644672 }, { target := 575, numerator := 7999667993306563990666088546304 }, { target := 578, numerator := 7999062961492139323857838276608 }, { target := 585, numerator := 213517489539050619544553914368 }, { target := 589, numerator := 5424159786936693030511024537600 }, { target := 592, numerator := 18620192130319092631055347220480 }, { target := 594, numerator := 5424159786936693030511024537600 }, { target := 599, numerator := 68376844357403426121381314560 }, { target := 601, numerator := 68376844357403426121381314560 }, { target := 613, numerator := 1084261389095968614210475130880 }, { target := 615, numerator := 1084261389095968614210475130880 }, { target := 618, numerator := 78144964979889629853007216640 }, { target := 620, numerator := 78144964979889629853007216640 }, { target := 694, numerator := 76191340855392389106682036224 }, { target := 696, numerator := 76191340855392389106682036224 }, { target := 708, numerator := 76191340855392389106682036224 }, { target := 710, numerator := 76191340855392389106682036224 }, { target := 739, numerator := 76191340855392389106682036224 }, { target := 741, numerator := 76191340855392389106682036224 }, { target := 753, numerator := 2438122907372556451413825159168 }, { target := 755, numerator := 2438122907372556451413825159168 }, { target := 758, numerator := 76191340855392389106682036224 }, { target := 760, numerator := 76191340855392389106682036224 }, { target := 763, numerator := 33972040279460243681417625600 }, { target := 766, numerator := 116620074243744199131141242880 }, { target := 768, numerator := 33972040279460243681417625600 }, { target := 773, numerator := 87913085602375833584633118720 }, { target := 775, numerator := 87913085602375833584633118720 }, { target := 778, numerator := 91820333851370315077283479552 }, { target := 780, numerator := 91820333851370315077283479552 }]

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
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot17.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 89653938782620899596210012160 }, { target := 11, numerator := 69730841275371810797052231680 }, { target := 12, numerator := 79692390028996355196631121920 }, { target := 13, numerator := 93638558284070717356041568256 }, { target := 14, numerator := 1105731911652324428353256816640 }, { target := 15, numerator := 2486402568904686282134891003904 }, { target := 16, numerator := 69730841275371810797052231680 }, { target := 17, numerator := 1105731911652324428353256816640 }, { target := 18, numerator := 79692390028996355196631121920 }, { target := 19, numerator := 77700080278271446316715343872 }, { target := 20, numerator := 77700080278271446316715343872 }, { target := 21, numerator := 77700080278271446316715343872 }, { target := 22, numerator := 2486402568904686282134891003904 }, { target := 23, numerator := 77700080278271446316715343872 }, { target := 24, numerator := 89653938782620899596210012160 }, { target := 25, numerator := 93638558284070717356041568256 }, { target := 26, numerator := 33945445364118824843456020480 }, { target := 27, numerator := 5419295069638991960528503439360 }, { target := 29, numerator := 54076415254277842576181307637760 }, { target := 37, numerator := 5419295069638991960528503439360 }, { target := 44, numerator := 33941572081900189651210076160 }, { target := 131, numerator := 14319423299447011710735482880 }, { target := 134, numerator := 48538977725303903091771310080 }, { target := 136, numerator := 14319423299447011710735482880 }, { target := 141, numerator := 89653938782620899596210012160 }, { target := 142, numerator := 69730841275371810797052231680 }, { target := 143, numerator := 79692390028996355196631121920 }, { target := 144, numerator := 93638558284070717356041568256 }, { target := 145, numerator := 1105731911652324428353256816640 }, { target := 146, numerator := 2486402568904686282134891003904 }, { target := 147, numerator := 69730841275371810797052231680 }, { target := 148, numerator := 1105731911652324428353256816640 }, { target := 149, numerator := 79692390028996355196631121920 }, { target := 150, numerator := 77700080278271446316715343872 }, { target := 151, numerator := 77700080278271446316715343872 }, { target := 152, numerator := 77700080278271446316715343872 }, { target := 153, numerator := 2486402568904686282134891003904 }, { target := 154, numerator := 77700080278271446316715343872 }, { target := 155, numerator := 89653938782620899596210012160 }, { target := 156, numerator := 93638558284070717356041568256 }, { target := 157, numerator := 116528778549517157142106210304 }, { target := 158, numerator := 18603492406435398377574580092928 }, { target := 160, numerator := 185634878267888976620687089205248 }, { target := 168, numerator := 18603492406435398377574580092928 }, { target := 175, numerator := 116515482248906760387525869568 }, { target := 227, numerator := 240566311430709796740356112384 }, { target := 230, numerator := 815454825785105571941758009344 }, { target := 232, numerator := 240566311430709796740356112384 }, { target := 253, numerator := 521227008099871226270771576832 }, { target := 256, numerator := 1766818789201062072540475686912 }, { target := 258, numerator := 521227008099871226270771576832 }, { target := 267, numerator := 33945445364118824843456020480 }, { target := 268, numerator := 5419295069638991960528503439360 }, { target := 270, numerator := 54076415254277842576181307637760 }, { target := 278, numerator := 5419295069638991960528503439360 }, { target := 285, numerator := 33941572081900189651210076160 }, { target := 302, numerator := 17183307959336414052882579456 }, { target := 305, numerator := 58246773270364683710125572096 }, { target := 307, numerator := 17183307959336414052882579456 }, { target := 328, numerator := 274932927349382624846121271296 }, { target := 331, numerator := 931948372325834939362009153536 }, { target := 333, numerator := 274932927349382624846121271296 }]

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
    Slot17.Left5.expected,
    Slot17.Left6.expected,
    Slot17.Left7.expected,
    Slot17.Left8.expected,
    Slot17.Left9.expected,
    Slot17.Left10.expected,
    Slot17.Left11.expected,
    Slot17.Left12.expected,
    Slot17.Left13.expected,
    Slot17.Left14.expected,
    Slot17.Left15.expected,
    Slot17.Left16.expected,
    Slot17.Left17.expected,
    Slot17.Left18.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 48381489525263277541111627776 }, { target := 27, numerator := 7145692813128889094281956950016 }, { target := 29, numerator := 74478361156798052183787480023040 }, { target := 37, numerator := 7145692813128889094281956950016 }, { target := 44, numerator := 48381489525263277541111627776 }, { target := 80, numerator := 80856155595717717250138963968 }, { target := 82, numerator := 2930253842271075658581153939456 }, { target := 85, numerator := 2930254919127926473445804605440 }, { target := 92, numerator := 80855078738866902385488297984 }, { target := 176, numerator := 2985910255817698367654791741440 }, { target := 178, numerator := 108210376010627550897607519764480 }, { target := 181, numerator := 108210415777518410422304322355200 }, { target := 188, numerator := 2985870488926838842957989150720 }, { target := 286, numerator := 2985909524643608122070283583488 }, { target := 288, numerator := 108210349512636500916817725751296 }, { target := 291, numerator := 108210389279517622533220246487040 }, { target := 298, numerator := 2985869757762486505667762847744 }, { target := 342, numerator := 20047192619225816395029676032 }, { target := 345, numerator := 67954568815425464328479834112 }, { target := 347, numerator := 20047192619225816395029676032 }, { target := 443, numerator := 521227008099871226270771576832 }, { target := 446, numerator := 1766818789201062072540475686912 }, { target := 448, numerator := 521227008099871226270771576832 }, { target := 469, numerator := 521227008099871226270771576832 }, { target := 472, numerator := 1766818789201062072540475686912 }, { target := 474, numerator := 521227008099871226270771576832 }, { target := 518, numerator := 274932927349382624846121271296 }, { target := 521, numerator := 931948372325834939362009153536 }, { target := 523, numerator := 274932927349382624846121271296 }, { target := 544, numerator := 6432284946111597660462378909696 }, { target := 547, numerator := 21803708794206513268823672487936 }, { target := 549, numerator := 6432284946111597660462378909696 }, { target := 558, numerator := 515499238780092421586477383680 }, { target := 561, numerator := 1747403198110940511303767162880 }, { target := 563, numerator := 515499238780092421586477383680 }, { target := 573, numerator := 80856886769807962834647121920 }, { target := 575, numerator := 2930280340262125639370947952640 }, { target := 578, numerator := 2930281417128714362529880473600 }, { target := 585, numerator := 80855809903219239675714600960 }, { target := 589, numerator := 240566311430709796740356112384 }, { target := 592, numerator := 815454825785105571941758009344 }, { target := 594, numerator := 240566311430709796740356112384 }, { target := 603, numerator := 521227008099871226270771576832 }, { target := 606, numerator := 1766818789201062072540475686912 }, { target := 608, numerator := 521227008099871226270771576832 }, { target := 658, numerator := 20047192619225816395029676032 }, { target := 661, numerator := 67954568815425464328479834112 }, { target := 663, numerator := 20047192619225816395029676032 }, { target := 684, numerator := 515499238780092421586477383680 }, { target := 687, numerator := 1747403198110940511303767162880 }, { target := 689, numerator := 515499238780092421586477383680 }, { target := 698, numerator := 20047192619225816395029676032 }, { target := 701, numerator := 67954568815425464328479834112 }, { target := 703, numerator := 20047192619225816395029676032 }, { target := 729, numerator := 521227008099871226270771576832 }, { target := 732, numerator := 1766818789201062072540475686912 }, { target := 734, numerator := 521227008099871226270771576832 }, { target := 743, numerator := 521227008099871226270771576832 }, { target := 746, numerator := 1766818789201062072540475686912 }, { target := 748, numerator := 521227008099871226270771576832 }, { target := 763, numerator := 17183307959336414052882579456 }, { target := 766, numerator := 58246773270364683710125572096 }, { target := 768, numerator := 17183307959336414052882579456 }]

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
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected,
    Slot22.Left2.expected,
    Slot22.Left3.expected,
    Slot22.Left4.expected,
    Slot22.Left5.expected,
    Slot22.Left6.expected,
    Slot22.Left7.expected,
    Slot22.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 3597763239173136423925579776 }, { target := 1, numerator := 86114203982789265372670328832 }, { target := 2, numerator := 64411567669067442428345057280 }, { target := 3, numerator := 74740629871854834097034625024 }, { target := 4, numerator := 3597763239173136423925579776 }, { target := 5, numerator := 74624572993171829696262832128 }, { target := 6, numerator := 74972743629220842898578210816 }, { target := 7, numerator := 3597763239173136423925579776 }, { target := 8, numerator := 86114203982789265372670328832 }, { target := 9, numerator := 3597763239173136423925579776 }, { target := 10, numerator := 113363697604530756872432517120 }, { target := 11, numerator := 9532667388299629502658762506240 }, { target := 16, numerator := 9532665088506604031886911078400 }, { target := 24, numerator := 113365997397556227644283944960 }, { target := 80, numerator := 3335791286701516162783510528 }, { target := 82, numerator := 116744378209306969303819485184 }, { target := 85, numerator := 116744435468000574098267701248 }, { target := 92, numerator := 3335762657354713765559402496 }, { target := 115, numerator := 3961252152958050443305418752 }, { target := 117, numerator := 138633949123552026048285638656 }, { target := 120, numerator := 138634017118250681741692895232 }, { target := 127, numerator := 3961218155608722596601790464 }, { target := 141, numerator := 113363643548520235686797770752 }, { target := 142, numerator := 9532662842770685708809959112704 }, { target := 147, numerator := 9532660542978756864547372400640 }, { target := 155, numerator := 113365943340449079949384482816 }, { target := 157, numerator := 175973906508475103829525790720 }, { target := 158, numerator := 25990425085594404200853819883520 }, { target := 160, numerator := 270893854069274934139744472268800 }, { target := 168, numerator := 25990425085594404200853819883520 }, { target := 175, numerator := 175973906508475103829525790720 }, { target := 176, numerator := 3023060853573249022522556416 }, { target := 178, numerator := 105799592752184440931586408448 }, { target := 181, numerator := 105799644642875520276555104256 }, { target := 188, numerator := 3023034908227709350038208512 }, { target := 211, numerator := 31168799835117291646008426496 }, { target := 213, numerator := 1090830283893211994432563314688 }, { target := 216, numerator := 1090830818904130364230688833536 }, { target := 223, numerator := 31168532329658106746945667072 }, { target := 237, numerator := 3752765197539205683131449344 }, { target := 239, numerator := 131337425485470340466796920832 }, { target := 242, numerator := 131337489901500645860551163904 }, { target := 249, numerator := 3752732989524052986254327808 }, { target := 267, numerator := 48381489525263277541111627776 }, { target := 268, numerator := 7145692813128889094281956950016 }, { target := 270, numerator := 74478361156798052183787480023040 }, { target := 278, numerator := 7145692813128889094281956950016 }, { target := 285, numerator := 48381489525263277541111627776 }, { target := 286, numerator := 3023060853573249022522556416 }, { target := 288, numerator := 105799592752184440931586408448 }, { target := 291, numerator := 105799644642875520276555104256 }, { target := 298, numerator := 3023034908227709350038208512 }, { target := 312, numerator := 3752765197539205683131449344 }, { target := 314, numerator := 131337425485470340466796920832 }, { target := 317, numerator := 131337489901500645860551163904 }, { target := 324, numerator := 3752732989524052986254327808 }, { target := 392, numerator := 3752765197539205683131449344 }, { target := 394, numerator := 131337425485470340466796920832 }, { target := 397, numerator := 131337489901500645860551163904 }, { target := 404, numerator := 3752732989524052986254327808 }, { target := 427, numerator := 160743442627929310094130413568 }, { target := 429, numerator := 5625619724960979583327801442304 }, { target := 432, numerator := 5625622484114277664360274853888 }, { target := 439, numerator := 160742063051280269577893707776 }]

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
    Slot22.Left9.expected,
    Slot22.Left10.expected,
    Slot22.Left11.expected,
    Slot22.Left12.expected,
    Slot22.Left13.expected,
    Slot22.Left14.expected,
    Slot22.Left15.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot25.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 27118831769720607911398342656 }, { target := 2, numerator := 262674986517616134551379116032 }, { target := 7, numerator := 27118831769720607911398342656 }, { target := 10, numerator := 31091269926827863421401169920 }, { target := 11, numerator := 2603245133672461361563935178752 }, { target := 16, numerator := 2603246075784574694058155311104 }, { target := 24, numerator := 31090327814714530927181037568 }, { target := 26, numerator := 6849262132654800249120882688 }, { target := 27, numerator := 718132781504713491016300101632 }, { target := 29, numerator := 7740753611750145810619170816000 }, { target := 37, numerator := 718133329314209824280336662528 }, { target := 44, numerator := 6849262132654800249120882688 }, { target := 141, numerator := 31091269926827863421401169920 }, { target := 142, numerator := 2603245133672461361563935178752 }, { target := 147, numerator := 2603246075784574694058155311104 }, { target := 155, numerator := 31090327814714530927181037568 }, { target := 157, numerator := 24502783055217122226110201856 }, { target := 158, numerator := 2569072610925063122233520553984 }, { target := 160, numerator := 27692034960718519033493716992000 }, { target := 168, numerator := 2569074570677366986675832487936 }, { target := 175, numerator := 24502783055217122226110201856 }, { target := 267, numerator := 6849259855679583171895099392 }, { target := 268, numerator := 718132542767968658158138687488 }, { target := 270, numerator := 7740751038406653608139423744000 }, { target := 278, numerator := 718133090577282877112243453952 }, { target := 285, numerator := 6849259855679583171895099392 }, { target := 453, numerator := 3752765197539205683131449344 }, { target := 455, numerator := 131337425485470340466796920832 }, { target := 458, numerator := 131337489901500645860551163904 }, { target := 465, numerator := 3752732989524052986254327808 }, { target := 502, numerator := 31168799835117291646008426496 }, { target := 504, numerator := 1090830283893211994432563314688 }, { target := 507, numerator := 1090830818904130364230688833536 }, { target := 514, numerator := 31168532329658106746945667072 }, { target := 528, numerator := 160743442627929310094130413568 }, { target := 530, numerator := 5625619724960979583327801442304 }, { target := 533, numerator := 5625622484114277664360274853888 }, { target := 540, numerator := 160742063051280269577893707776 }, { target := 573, numerator := 3335791286701516162783510528 }, { target := 575, numerator := 116744378209306969303819485184 }, { target := 578, numerator := 116744435468000574098267701248 }, { target := 585, numerator := 3335762657354713765559402496 }, { target := 642, numerator := 3752765197539205683131449344 }, { target := 644, numerator := 131337425485470340466796920832 }, { target := 647, numerator := 131337489901500645860551163904 }, { target := 654, numerator := 3752732989524052986254327808 }, { target := 668, numerator := 3752765197539205683131449344 }, { target := 670, numerator := 131337425485470340466796920832 }, { target := 673, numerator := 131337489901500645860551163904 }, { target := 680, numerator := 3752732989524052986254327808 }, { target := 713, numerator := 3961252152958050443305418752 }, { target := 715, numerator := 138633949123552026048285638656 }, { target := 718, numerator := 138634017118250681741692895232 }, { target := 725, numerator := 3961218155608722596601790464 }]

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
    Slot26.Left0.expected,
    Slot26.Left1.expected,
    Slot26.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 5950181768415752969256960 }, { target := 27, numerator := 158671513824420079180185600 }, { target := 28, numerator := 151729635094601700716052480 }, { target := 29, numerator := 4958484807013127474380800 }, { target := 30, numerator := 155696422940212202695557120 }, { target := 31, numerator := 4958484807013127474380800 }, { target := 32, numerator := 151729635094601700716052480 }, { target := 33, numerator := 86277635642028418054225920 }, { target := 34, numerator := 155696422940212202695557120 }, { target := 35, numerator := 2430649252397835087941468160 }, { target := 36, numerator := 95202908294652047508111360 }, { target := 37, numerator := 158671513824420079180185600 }, { target := 38, numerator := 151729635094601700716052480 }, { target := 39, numerator := 4958484807013127474380800 }, { target := 40, numerator := 95202908294652047508111360 }, { target := 41, numerator := 4958484807013127474380800 }, { target := 42, numerator := 152721332056004326210928640 }, { target := 43, numerator := 86277635642028418054225920 }, { target := 44, numerator := 5950181768415752969256960 }, { target := 61, numerator := 105913235477800402852773888 }, { target := 62, numerator := 2824352946074677409407303680 }, { target := 63, numerator := 2700787504683910272745734144 }, { target := 64, numerator := 88261029564833669043978240 }, { target := 65, numerator := 2771396328335777207980916736 }, { target := 66, numerator := 88261029564833669043978240 }, { target := 67, numerator := 2700787504683910272745734144 }, { target := 68, numerator := 1535741914428105841365221376 }, { target := 69, numerator := 2771396328335777207980916736 }, { target := 70, numerator := 43265556692681464565358133248 }, { target := 71, numerator := 1694611767644806445644382208 }, { target := 72, numerator := 2824352946074677409407303680 }, { target := 73, numerator := 2700787504683910272745734144 }, { target := 74, numerator := 88261029564833669043978240 }, { target := 75, numerator := 1694611767644806445644382208 }, { target := 76, numerator := 88261029564833669043978240 }, { target := 77, numerator := 2718439710596877006554529792 }, { target := 78, numerator := 1535741914428105841365221376 }, { target := 79, numerator := 105913235477800402852773888 }, { target := 96, numerator := 5950181768415752969256960 }, { target := 97, numerator := 158671513824420079180185600 }, { target := 98, numerator := 151729635094601700716052480 }, { target := 99, numerator := 4958484807013127474380800 }, { target := 100, numerator := 155696422940212202695557120 }, { target := 101, numerator := 4958484807013127474380800 }, { target := 102, numerator := 151729635094601700716052480 }, { target := 103, numerator := 86277635642028418054225920 }, { target := 104, numerator := 155696422940212202695557120 }, { target := 105, numerator := 2430649252397835087941468160 }, { target := 106, numerator := 95202908294652047508111360 }, { target := 107, numerator := 158671513824420079180185600 }, { target := 108, numerator := 151729635094601700716052480 }, { target := 109, numerator := 4958484807013127474380800 }, { target := 110, numerator := 95202908294652047508111360 }, { target := 111, numerator := 4958484807013127474380800 }, { target := 112, numerator := 152721332056004326210928640 }, { target := 113, numerator := 86277635642028418054225920 }, { target := 114, numerator := 5950181768415752969256960 }]

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
    Slot26.Left3.expected,
    Slot26.Left4.expected,
    Slot26.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 157, numerator := 94211211333249422013235200 }, { target := 158, numerator := 2512298968886651253686272000 }, { target := 159, numerator := 2402385888997860261337497600 }, { target := 160, numerator := 78509342777707851677696000 }, { target := 161, numerator := 2465193363220026542679654400 }, { target := 162, numerator := 78509342777707851677696000 }, { target := 163, numerator := 2402385888997860261337497600 }, { target := 164, numerator := 1366062564332116619191910400 }, { target := 165, numerator := 2465193363220026542679654400 }, { target := 166, numerator := 38485279829632388892406579200 }, { target := 167, numerator := 1507379381331990752211763200 }, { target := 168, numerator := 2512298968886651253686272000 }, { target := 169, numerator := 2402385888997860261337497600 }, { target := 170, numerator := 78509342777707851677696000 }, { target := 171, numerator := 1507379381331990752211763200 }, { target := 172, numerator := 78509342777707851677696000 }, { target := 173, numerator := 2418087757553401831673036800 }, { target := 174, numerator := 1366062564332116619191910400 }, { target := 175, numerator := 94211211333249422013235200 }, { target := 192, numerator := 160853247139505855268913152 }, { target := 193, numerator := 4289419923720156140504350720 }, { target := 194, numerator := 4101757802057399309357285376 }, { target := 195, numerator := 134044372616254879390760960 }, { target := 196, numerator := 4208993300150403212869894144 }, { target := 197, numerator := 134044372616254879390760960 }, { target := 198, numerator := 4101757802057399309357285376 }, { target := 199, numerator := 2332372083522834901399240704 }, { target := 200, numerator := 4208993300150403212869894144 }, { target := 201, numerator := 65708551456488141877351022592 }, { target := 202, numerator := 2573651954232093684302610432 }, { target := 203, numerator := 4289419923720156140504350720 }, { target := 204, numerator := 4101757802057399309357285376 }, { target := 205, numerator := 134044372616254879390760960 }, { target := 206, numerator := 2573651954232093684302610432 }, { target := 207, numerator := 134044372616254879390760960 }, { target := 208, numerator := 4128566676580650285235437568 }, { target := 209, numerator := 2332372083522834901399240704 }, { target := 210, numerator := 160853247139505855268913152 }, { target := 267, numerator := 5950181768415752969256960 }, { target := 268, numerator := 158671513824420079180185600 }, { target := 269, numerator := 151729635094601700716052480 }, { target := 270, numerator := 4958484807013127474380800 }, { target := 271, numerator := 155696422940212202695557120 }, { target := 272, numerator := 4958484807013127474380800 }, { target := 273, numerator := 151729635094601700716052480 }, { target := 274, numerator := 86277635642028418054225920 }, { target := 275, numerator := 155696422940212202695557120 }, { target := 276, numerator := 2430649252397835087941468160 }, { target := 277, numerator := 95202908294652047508111360 }, { target := 278, numerator := 158671513824420079180185600 }, { target := 279, numerator := 151729635094601700716052480 }, { target := 280, numerator := 4958484807013127474380800 }, { target := 281, numerator := 95202908294652047508111360 }, { target := 282, numerator := 4958484807013127474380800 }, { target := 283, numerator := 152721332056004326210928640 }, { target := 284, numerator := 86277635642028418054225920 }, { target := 285, numerator := 5950181768415752969256960 }]

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
    Slot26.Left6.expected,
    Slot26.Left7.expected,
    Slot26.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 373, numerator := 160853247139505855268913152 }, { target := 374, numerator := 4289419923720156140504350720 }, { target := 375, numerator := 4101757802057399309357285376 }, { target := 376, numerator := 134044372616254879390760960 }, { target := 377, numerator := 4208993300150403212869894144 }, { target := 378, numerator := 134044372616254879390760960 }, { target := 379, numerator := 4101757802057399309357285376 }, { target := 380, numerator := 2332372083522834901399240704 }, { target := 381, numerator := 4208993300150403212869894144 }, { target := 382, numerator := 65708551456488141877351022592 }, { target := 383, numerator := 2573651954232093684302610432 }, { target := 384, numerator := 4289419923720156140504350720 }, { target := 385, numerator := 4101757802057399309357285376 }, { target := 386, numerator := 134044372616254879390760960 }, { target := 387, numerator := 2573651954232093684302610432 }, { target := 388, numerator := 134044372616254879390760960 }, { target := 389, numerator := 4128566676580650285235437568 }, { target := 390, numerator := 2332372083522834901399240704 }, { target := 391, numerator := 160853247139505855268913152 }, { target := 408, numerator := 160853247139505855268913152 }, { target := 409, numerator := 4289419923720156140504350720 }, { target := 410, numerator := 4101757802057399309357285376 }, { target := 411, numerator := 134044372616254879390760960 }, { target := 412, numerator := 4208993300150403212869894144 }, { target := 413, numerator := 134044372616254879390760960 }, { target := 414, numerator := 4101757802057399309357285376 }, { target := 415, numerator := 2332372083522834901399240704 }, { target := 416, numerator := 4208993300150403212869894144 }, { target := 417, numerator := 65708551456488141877351022592 }, { target := 418, numerator := 2573651954232093684302610432 }, { target := 419, numerator := 4289419923720156140504350720 }, { target := 420, numerator := 4101757802057399309357285376 }, { target := 421, numerator := 134044372616254879390760960 }, { target := 422, numerator := 2573651954232093684302610432 }, { target := 423, numerator := 134044372616254879390760960 }, { target := 424, numerator := 4128566676580650285235437568 }, { target := 425, numerator := 2332372083522834901399240704 }, { target := 426, numerator := 160853247139505855268913152 }, { target := 483, numerator := 105913235477800402852773888 }, { target := 484, numerator := 2824352946074677409407303680 }, { target := 485, numerator := 2700787504683910272745734144 }, { target := 486, numerator := 88261029564833669043978240 }, { target := 487, numerator := 2771396328335777207980916736 }, { target := 488, numerator := 88261029564833669043978240 }, { target := 489, numerator := 2700787504683910272745734144 }, { target := 490, numerator := 1535741914428105841365221376 }, { target := 491, numerator := 2771396328335777207980916736 }, { target := 492, numerator := 43265556692681464565358133248 }, { target := 493, numerator := 1694611767644806445644382208 }, { target := 494, numerator := 2824352946074677409407303680 }, { target := 495, numerator := 2700787504683910272745734144 }, { target := 496, numerator := 88261029564833669043978240 }, { target := 497, numerator := 1694611767644806445644382208 }, { target := 498, numerator := 88261029564833669043978240 }, { target := 499, numerator := 2718439710596877006554529792 }, { target := 500, numerator := 1535741914428105841365221376 }, { target := 501, numerator := 105913235477800402852773888 }]

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
    Slot26.Left9.expected,
    Slot27.Left0.expected,
    Slot27.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 1353996917968384675670917120 }, { target := 11, numerator := 1392682544196052809261514752 }, { target := 12, numerator := 1353996917968384675670917120 }, { target := 13, numerator := 1199254413057712141308526592 }, { target := 14, numerator := 56132843656346461839957164032 }, { target := 15, numerator := 15280822359928912768286064640 }, { target := 16, numerator := 1392682544196052809261514752 }, { target := 17, numerator := 56132843656346461839957164032 }, { target := 18, numerator := 1353996917968384675670917120 }, { target := 19, numerator := 1353996917968384675670917120 }, { target := 20, numerator := 1160568786830044007717928960 }, { target := 21, numerator := 1353996917968384675670917120 }, { target := 22, numerator := 15280822359928912768286064640 }, { target := 23, numerator := 1160568786830044007717928960 }, { target := 24, numerator := 1353996917968384675670917120 }, { target := 25, numerator := 1199254413057712141308526592 }, { target := 141, numerator := 1353996917968384675670917120 }, { target := 142, numerator := 1392682544196052809261514752 }, { target := 143, numerator := 1353996917968384675670917120 }, { target := 144, numerator := 1199254413057712141308526592 }, { target := 145, numerator := 56132843656346461839957164032 }, { target := 146, numerator := 15280822359928912768286064640 }, { target := 147, numerator := 1392682544196052809261514752 }, { target := 148, numerator := 56132843656346461839957164032 }, { target := 149, numerator := 1353996917968384675670917120 }, { target := 150, numerator := 1353996917968384675670917120 }, { target := 151, numerator := 1160568786830044007717928960 }, { target := 152, numerator := 1353996917968384675670917120 }, { target := 153, numerator := 15280822359928912768286064640 }, { target := 154, numerator := 1160568786830044007717928960 }, { target := 155, numerator := 1353996917968384675670917120 }, { target := 156, numerator := 1199254413057712141308526592 }, { target := 623, numerator := 5950181768415752969256960 }, { target := 624, numerator := 158671513824420079180185600 }, { target := 625, numerator := 151729635094601700716052480 }, { target := 626, numerator := 4958484807013127474380800 }, { target := 627, numerator := 155696422940212202695557120 }, { target := 628, numerator := 4958484807013127474380800 }, { target := 629, numerator := 151729635094601700716052480 }, { target := 630, numerator := 86277635642028418054225920 }, { target := 631, numerator := 155696422940212202695557120 }, { target := 632, numerator := 2430649252397835087941468160 }, { target := 633, numerator := 95202908294652047508111360 }, { target := 634, numerator := 158671513824420079180185600 }, { target := 635, numerator := 151729635094601700716052480 }, { target := 636, numerator := 4958484807013127474380800 }, { target := 637, numerator := 95202908294652047508111360 }, { target := 638, numerator := 4958484807013127474380800 }, { target := 639, numerator := 152721332056004326210928640 }, { target := 640, numerator := 86277635642028418054225920 }, { target := 641, numerator := 5950181768415752969256960 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent1
