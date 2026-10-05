import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 56; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left1.expected,
    Slot0.Left2.expected,
    Slot0.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 67322056579789662166450176 }, { target := 111, numerator := 76672342215871559689568256 }, { target := 112, numerator := 59841828070924144147955712 }, { target := 113, numerator := 802254507575826807483531264 }, { target := 114, numerator := 71062170834222421175697408 }, { target := 115, numerator := 59841828070924144147955712 }, { target := 116, numerator := 71062170834222421175697408 }, { target := 117, numerator := 69192113707006041671073792 }, { target := 118, numerator := 2614339863848498547463815168 }, { target := 119, numerator := 69192113707006041671073792 }, { target := 120, numerator := 802254507575826807483531264 }, { target := 121, numerator := 2614339863848498547463815168 }, { target := 122, numerator := 67322056579789662166450176 }, { target := 123, numerator := 69192113707006041671073792 }, { target := 124, numerator := 69192113707006041671073792 }, { target := 125, numerator := 76672342215871559689568256 }, { target := 206, numerator := 976169820406950101413527552 }, { target := 207, numerator := 1111748962130137615498739712 }, { target := 208, numerator := 867706507028400090145357824 }, { target := 209, numerator := 11632690359849488708511203328 }, { target := 210, numerator := 1030401477096225107047612416 }, { target := 211, numerator := 867706507028400090145357824 }, { target := 212, numerator := 1030401477096225107047612416 }, { target := 213, numerator := 1003285648751587604230569984 }, { target := 214, numerator := 37907928025803228938225319936 }, { target := 215, numerator := 1003285648751587604230569984 }, { target := 216, numerator := 11632690359849488708511203328 }, { target := 217, numerator := 37907928025803228938225319936 }, { target := 218, numerator := 976169820406950101413527552 }, { target := 219, numerator := 1003285648751587604230569984 }, { target := 220, numerator := 1003285648751587604230569984 }, { target := 221, numerator := 1111748962130137615498739712 }, { target := 241, numerator := 1727932785547934662272221184 }, { target := 242, numerator := 1967923450207370032032251904 }, { target := 243, numerator := 1535940253820386366464196608 }, { target := 244, numerator := 20591199027779554725410635776 }, { target := 245, numerator := 1823929051411708810176233472 }, { target := 246, numerator := 1535940253820386366464196608 }, { target := 247, numerator := 1823929051411708810176233472 }, { target := 248, numerator := 1775930918479821736224227328 }, { target := 249, numerator := 67101389838778129384904589312 }, { target := 250, numerator := 1775930918479821736224227328 }, { target := 251, numerator := 20591199027779554725410635776 }, { target := 252, numerator := 67101389838778129384904589312 }, { target := 253, numerator := 1727932785547934662272221184 }, { target := 254, numerator := 1775930918479821736224227328 }, { target := 255, numerator := 1775930918479821736224227328 }, { target := 256, numerator := 1967923450207370032032251904 }, { target := 302, numerator := 56101713816491385138708480 }, { target := 303, numerator := 63893618513226299741306880 }, { target := 304, numerator := 49868190059103453456629760 }, { target := 305, numerator := 668545422979855672902942720 }, { target := 306, numerator := 59218475695185350979747840 }, { target := 307, numerator := 49868190059103453456629760 }, { target := 308, numerator := 59218475695185350979747840 }, { target := 309, numerator := 57660094755838368059228160 }, { target := 310, numerator := 2178616553207082122886512640 }, { target := 311, numerator := 57660094755838368059228160 }, { target := 312, numerator := 668545422979855672902942720 }, { target := 313, numerator := 2178616553207082122886512640 }, { target := 314, numerator := 56101713816491385138708480 }, { target := 315, numerator := 57660094755838368059228160 }, { target := 316, numerator := 57660094755838368059228160 }, { target := 317, numerator := 63893618513226299741306880 }]

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
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 337, numerator := 1077152905276634594663202816 }, { target := 338, numerator := 1226757475453944955033092096 }, { target := 339, numerator := 957469249134786306367291392 }, { target := 340, numerator := 12836072121213228919736500224 }, { target := 341, numerator := 1136994733347558738811158528 }, { target := 342, numerator := 957469249134786306367291392 }, { target := 343, numerator := 1136994733347558738811158528 }, { target := 344, numerator := 1107073819312096666737180672 }, { target := 345, numerator := 41829437821575976759421042688 }, { target := 346, numerator := 1107073819312096666737180672 }, { target := 347, numerator := 12836072121213228919736500224 }, { target := 348, numerator := 41829437821575976759421042688 }, { target := 349, numerator := 1077152905276634594663202816 }, { target := 350, numerator := 1107073819312096666737180672 }, { target := 351, numerator := 1107073819312096666737180672 }, { target := 352, numerator := 1226757475453944955033092096 }, { target := 363, numerator := 56101713816491385138708480 }, { target := 364, numerator := 63893618513226299741306880 }, { target := 365, numerator := 49868190059103453456629760 }, { target := 366, numerator := 668545422979855672902942720 }, { target := 367, numerator := 59218475695185350979747840 }, { target := 368, numerator := 49868190059103453456629760 }, { target := 369, numerator := 59218475695185350979747840 }, { target := 370, numerator := 57660094755838368059228160 }, { target := 371, numerator := 2178616553207082122886512640 }, { target := 372, numerator := 57660094755838368059228160 }, { target := 373, numerator := 668545422979855672902942720 }, { target := 374, numerator := 2178616553207082122886512640 }, { target := 375, numerator := 56101713816491385138708480 }, { target := 376, numerator := 57660094755838368059228160 }, { target := 377, numerator := 57660094755838368059228160 }, { target := 378, numerator := 63893618513226299741306880 }, { target := 473, numerator := 1716712442784636385244479488 }, { target := 474, numerator := 1955144726504724772083990528 }, { target := 475, numerator := 1525966615808565675772870656 }, { target := 476, numerator := 20457489943183583590830047232 }, { target := 477, numerator := 1812085356272671739980283904 }, { target := 478, numerator := 1525966615808565675772870656 }, { target := 479, numerator := 1812085356272671739980283904 }, { target := 480, numerator := 1764398899528654062612381696 }, { target := 481, numerator := 66665666528136712960327286784 }, { target := 482, numerator := 1764398899528654062612381696 }, { target := 483, numerator := 20457489943183583590830047232 }, { target := 484, numerator := 66665666528136712960327286784 }, { target := 485, numerator := 1716712442784636385244479488 }, { target := 486, numerator := 1764398899528654062612381696 }, { target := 487, numerator := 1764398899528654062612381696 }, { target := 488, numerator := 1955144726504724772083990528 }, { target := 508, numerator := 1795254842127724324438671360 }, { target := 509, numerator := 2044595792423241591721820160 }, { target := 510, numerator := 1595782081891310510612152320 }, { target := 511, numerator := 21393453535355381532894167040 }, { target := 512, numerator := 1894991222245931231351930880 }, { target := 513, numerator := 1595782081891310510612152320 }, { target := 514, numerator := 1894991222245931231351930880 }, { target := 515, numerator := 1845123032186827777895301120 }, { target := 516, numerator := 69715729702626627932368404480 }, { target := 517, numerator := 1845123032186827777895301120 }, { target := 518, numerator := 21393453535355381532894167040 }, { target := 519, numerator := 69715729702626627932368404480 }, { target := 520, numerator := 1795254842127724324438671360 }, { target := 521, numerator := 1845123032186827777895301120 }, { target := 522, numerator := 1845123032186827777895301120 }, { target := 523, numerator := 2044595792423241591721820160 }]

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
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 569, numerator := 1077152905276634594663202816 }, { target := 570, numerator := 1226757475453944955033092096 }, { target := 571, numerator := 957469249134786306367291392 }, { target := 572, numerator := 12836072121213228919736500224 }, { target := 573, numerator := 1136994733347558738811158528 }, { target := 574, numerator := 957469249134786306367291392 }, { target := 575, numerator := 1136994733347558738811158528 }, { target := 576, numerator := 1107073819312096666737180672 }, { target := 577, numerator := 41829437821575976759421042688 }, { target := 578, numerator := 1107073819312096666737180672 }, { target := 579, numerator := 12836072121213228919736500224 }, { target := 580, numerator := 41829437821575976759421042688 }, { target := 581, numerator := 1077152905276634594663202816 }, { target := 582, numerator := 1107073819312096666737180672 }, { target := 583, numerator := 1107073819312096666737180672 }, { target := 584, numerator := 1226757475453944955033092096 }, { target := 604, numerator := 27501060112844076994994896896 }, { target := 605, numerator := 31320651795183532133188632576 }, { target := 606, numerator := 24445386766972512884439908352 }, { target := 607, numerator := 327720966344725250857022521344 }, { target := 608, numerator := 29028896785779859050272391168 }, { target := 609, numerator := 24445386766972512884439908352 }, { target := 610, numerator := 29028896785779859050272391168 }, { target := 611, numerator := 28264978449311968022633644032 }, { target := 612, numerator := 1067957834382111656638968496128 }, { target := 613, numerator := 28264978449311968022633644032 }, { target := 614, numerator := 327720966344725250857022521344 }, { target := 615, numerator := 1067957834382111656638968496128 }, { target := 616, numerator := 27501060112844076994994896896 }, { target := 617, numerator := 28264978449311968022633644032 }, { target := 618, numerator := 28264978449311968022633644032 }, { target := 619, numerator := 31320651795183532133188632576 }, { target := 630, numerator := 1761593813837829493355446272 }, { target := 631, numerator := 2006259621315305811877036032 }, { target := 632, numerator := 1565861167855848438538174464 }, { target := 633, numerator := 20992326281567468129152401408 }, { target := 634, numerator := 1859460136828820020764082176 }, { target := 635, numerator := 1565861167855848438538174464 }, { target := 636, numerator := 1859460136828820020764082176 }, { target := 637, numerator := 1810526975333324757059764224 }, { target := 638, numerator := 68408559770702378658636496896 }, { target := 639, numerator := 1810526975333324757059764224 }, { target := 640, numerator := 20992326281567468129152401408 }, { target := 641, numerator := 68408559770702378658636496896 }, { target := 642, numerator := 1761593813837829493355446272 }, { target := 643, numerator := 1810526975333324757059764224 }, { target := 644, numerator := 1810526975333324757059764224 }, { target := 645, numerator := 2006259621315305811877036032 }, { target := 679, numerator := 976169820406950101413527552 }, { target := 680, numerator := 1111748962130137615498739712 }, { target := 681, numerator := 867706507028400090145357824 }, { target := 682, numerator := 11632690359849488708511203328 }, { target := 683, numerator := 1030401477096225107047612416 }, { target := 684, numerator := 867706507028400090145357824 }, { target := 685, numerator := 1030401477096225107047612416 }, { target := 686, numerator := 1003285648751587604230569984 }, { target := 687, numerator := 37907928025803228938225319936 }, { target := 688, numerator := 1003285648751587604230569984 }, { target := 689, numerator := 11632690359849488708511203328 }, { target := 690, numerator := 37907928025803228938225319936 }, { target := 691, numerator := 976169820406950101413527552 }, { target := 692, numerator := 1003285648751587604230569984 }, { target := 693, numerator := 1003285648751587604230569984 }, { target := 694, numerator := 1111748962130137615498739712 }]

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
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 705, numerator := 1716712442784636385244479488 }, { target := 706, numerator := 1955144726504724772083990528 }, { target := 707, numerator := 1525966615808565675772870656 }, { target := 708, numerator := 20457489943183583590830047232 }, { target := 709, numerator := 1812085356272671739980283904 }, { target := 710, numerator := 1525966615808565675772870656 }, { target := 711, numerator := 1812085356272671739980283904 }, { target := 712, numerator := 1764398899528654062612381696 }, { target := 713, numerator := 66665666528136712960327286784 }, { target := 714, numerator := 1764398899528654062612381696 }, { target := 715, numerator := 20457489943183583590830047232 }, { target := 716, numerator := 66665666528136712960327286784 }, { target := 717, numerator := 1716712442784636385244479488 }, { target := 718, numerator := 1764398899528654062612381696 }, { target := 719, numerator := 1764398899528654062612381696 }, { target := 720, numerator := 1955144726504724772083990528 }, { target := 785, numerator := 56101713816491385138708480 }, { target := 786, numerator := 63893618513226299741306880 }, { target := 787, numerator := 49868190059103453456629760 }, { target := 788, numerator := 668545422979855672902942720 }, { target := 789, numerator := 59218475695185350979747840 }, { target := 790, numerator := 49868190059103453456629760 }, { target := 791, numerator := 59218475695185350979747840 }, { target := 792, numerator := 57660094755838368059228160 }, { target := 793, numerator := 2178616553207082122886512640 }, { target := 794, numerator := 57660094755838368059228160 }, { target := 795, numerator := 668545422979855672902942720 }, { target := 796, numerator := 2178616553207082122886512640 }, { target := 797, numerator := 56101713816491385138708480 }, { target := 798, numerator := 57660094755838368059228160 }, { target := 799, numerator := 57660094755838368059228160 }, { target := 800, numerator := 63893618513226299741306880 }, { target := 820, numerator := 1761593813837829493355446272 }, { target := 821, numerator := 2006259621315305811877036032 }, { target := 822, numerator := 1565861167855848438538174464 }, { target := 823, numerator := 20992326281567468129152401408 }, { target := 824, numerator := 1859460136828820020764082176 }, { target := 825, numerator := 1565861167855848438538174464 }, { target := 826, numerator := 1859460136828820020764082176 }, { target := 827, numerator := 1810526975333324757059764224 }, { target := 828, numerator := 68408559770702378658636496896 }, { target := 829, numerator := 1810526975333324757059764224 }, { target := 830, numerator := 20992326281567468129152401408 }, { target := 831, numerator := 68408559770702378658636496896 }, { target := 832, numerator := 1761593813837829493355446272 }, { target := 833, numerator := 1810526975333324757059764224 }, { target := 834, numerator := 1810526975333324757059764224 }, { target := 835, numerator := 2006259621315305811877036032 }, { target := 846, numerator := 56101713816491385138708480 }, { target := 847, numerator := 63893618513226299741306880 }, { target := 848, numerator := 49868190059103453456629760 }, { target := 849, numerator := 668545422979855672902942720 }, { target := 850, numerator := 59218475695185350979747840 }, { target := 851, numerator := 49868190059103453456629760 }, { target := 852, numerator := 59218475695185350979747840 }, { target := 853, numerator := 57660094755838368059228160 }, { target := 854, numerator := 2178616553207082122886512640 }, { target := 855, numerator := 57660094755838368059228160 }, { target := 856, numerator := 668545422979855672902942720 }, { target := 857, numerator := 2178616553207082122886512640 }, { target := 858, numerator := 56101713816491385138708480 }, { target := 859, numerator := 57660094755838368059228160 }, { target := 860, numerator := 57660094755838368059228160 }, { target := 861, numerator := 63893618513226299741306880 }]

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
    Slot0.Left16.expected,
    Slot0.Left17.expected,
    Slot0.Left18.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 8845822710365603152170844160 }, { target := 260, numerator := 32309529458831945770205184000 }, { target := 262, numerator := 8845819730063513743471411200 }, { target := 353, numerator := 6587314784314810857999564800 }, { target := 356, numerator := 24060287894874853233131520000 }, { target := 358, numerator := 6587312564940914489819136000 }, { target := 379, numerator := 6963732771989942907028111360 }, { target := 382, numerator := 25435161488867701989310464000 }, { target := 384, numerator := 6963730425794681032094515200 }, { target := 524, numerator := 9034031704203169176685117440 }, { target := 527, numerator := 32996966255828370148294656000 }, { target := 529, numerator := 9034028660490397014609100800 }, { target := 620, numerator := 121018383037554953762677719040 }, { target := 623, numerator := 442021860468700875111530496000 }, { target := 625, numerator := 121018342264485943341534412800 }, { target := 895, numerator := 1716712442784636385244479488 }, { target := 896, numerator := 1955144726504724772083990528 }, { target := 897, numerator := 1525966615808565675772870656 }, { target := 898, numerator := 20457489943183583590830047232 }, { target := 899, numerator := 1812085356272671739980283904 }, { target := 900, numerator := 1525966615808565675772870656 }, { target := 901, numerator := 1812085356272671739980283904 }, { target := 902, numerator := 1764398899528654062612381696 }, { target := 903, numerator := 66665666528136712960327286784 }, { target := 904, numerator := 1764398899528654062612381696 }, { target := 905, numerator := 20457489943183583590830047232 }, { target := 906, numerator := 66665666528136712960327286784 }, { target := 907, numerator := 1716712442784636385244479488 }, { target := 908, numerator := 1764398899528654062612381696 }, { target := 909, numerator := 1764398899528654062612381696 }, { target := 910, numerator := 1955144726504724772083990528 }, { target := 921, numerator := 1795254842127724324438671360 }, { target := 922, numerator := 2044595792423241591721820160 }, { target := 923, numerator := 1595782081891310510612152320 }, { target := 924, numerator := 21393453535355381532894167040 }, { target := 925, numerator := 1894991222245931231351930880 }, { target := 926, numerator := 1595782081891310510612152320 }, { target := 927, numerator := 1894991222245931231351930880 }, { target := 928, numerator := 1845123032186827777895301120 }, { target := 929, numerator := 69715729702626627932368404480 }, { target := 930, numerator := 1845123032186827777895301120 }, { target := 931, numerator := 21393453535355381532894167040 }, { target := 932, numerator := 69715729702626627932368404480 }, { target := 933, numerator := 1795254842127724324438671360 }, { target := 934, numerator := 1845123032186827777895301120 }, { target := 935, numerator := 1845123032186827777895301120 }, { target := 936, numerator := 2044595792423241591721820160 }, { target := 966, numerator := 67322056579789662166450176 }, { target := 967, numerator := 76672342215871559689568256 }, { target := 968, numerator := 59841828070924144147955712 }, { target := 969, numerator := 802254507575826807483531264 }, { target := 970, numerator := 71062170834222421175697408 }, { target := 971, numerator := 59841828070924144147955712 }, { target := 972, numerator := 71062170834222421175697408 }, { target := 973, numerator := 69192113707006041671073792 }, { target := 974, numerator := 2614339863848498547463815168 }, { target := 975, numerator := 69192113707006041671073792 }, { target := 976, numerator := 802254507575826807483531264 }, { target := 977, numerator := 2614339863848498547463815168 }, { target := 978, numerator := 67322056579789662166450176 }, { target := 979, numerator := 69192113707006041671073792 }, { target := 980, numerator := 69192113707006041671073792 }, { target := 981, numerator := 76672342215871559689568256 }]

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
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 389, numerator := 1798881405143168355089252352 }, { target := 391, numerator := 1798881834029968068836327424 }, { target := 646, numerator := 218887059833089286510099824640 }, { target := 649, numerator := 799488994906841551718055936000 }, { target := 651, numerator := 218886986086465244333133004800 }, { target := 656, numerator := 44101608642219611286059089920 }, { target := 658, numerator := 44101619156863733300503511040 }, { target := 695, numerator := 6587314784314810857999564800 }, { target := 698, numerator := 24060287894874853233131520000 }, { target := 700, numerator := 6587312564940914489819136000 }, { target := 721, numerator := 121018383037554953762677719040 }, { target := 724, numerator := 442021860468700875111530496000 }, { target := 726, numerator := 121018342264485943341534412800 }, { target := 731, numerator := 32611979022272923082585800704 }, { target := 733, numerator := 32611986797575550151161806848 }, { target := 735, numerator := 7151941765827508931542384640 }, { target := 738, numerator := 26122598285864126367399936000 }, { target := 740, numerator := 7151939356221564303232204800 }, { target := 745, numerator := 36383827129831179310998749184 }, { target := 747, numerator := 36383835804412579972915396608 }, { target := 749, numerator := 19884411881021420665567182848 }, { target := 836, numerator := 7151941765827508931542384640 }, { target := 839, numerator := 26122598285864126367399936000 }, { target := 841, numerator := 7151939356221564303232204800 }, { target := 862, numerator := 6963732771989942907028111360 }, { target := 865, numerator := 25435161488867701989310464000 }, { target := 867, numerator := 6963730425794681032094515200 }, { target := 872, numerator := 1798881405143168355089252352 }, { target := 874, numerator := 1798881834029968068836327424 }, { target := 911, numerator := 6963732771989942907028111360 }, { target := 914, numerator := 25435161488867701989310464000 }, { target := 916, numerator := 6963730425794681032094515200 }, { target := 937, numerator := 218887059833089286510099824640 }, { target := 940, numerator := 799488994906841551718055936000 }, { target := 942, numerator := 218886986086465244333133004800 }, { target := 947, numerator := 36325798697407206138253934592 }, { target := 949, numerator := 36325807358153548744888418304 }, { target := 951, numerator := 6963732771989942907028111360 }, { target := 954, numerator := 25435161488867701989310464000 }, { target := 956, numerator := 6963730425794681032094515200 }, { target := 961, numerator := 36964111454070911038446895104 }, { target := 963, numerator := 36964120267002892253185179648 }, { target := 965, numerator := 19826383441679918465181286400 }, { target := 982, numerator := 8845822710365603152170844160 }, { target := 985, numerator := 32309529458831945770205184000 }, { target := 987, numerator := 8845819730063513743471411200 }, { target := 992, numerator := 1798881405143168355089252352 }, { target := 994, numerator := 1798881834029968068836327424 }, { target := 996, numerator := 9034031704203169176685117440 }, { target := 999, numerator := 32996966255828370148294656000 }, { target := 1001, numerator := 9034028660490397014609100800 }, { target := 1006, numerator := 44101608642219611286059089920 }, { target := 1008, numerator := 44101619156863733300503511040 }, { target := 1010, numerator := 19690983749883079997614194688 }, { target := 1011, numerator := 1798881405143168355089252352 }, { target := 1013, numerator := 1798881834029968068836327424 }, { target := 1015, numerator := 19826383441679918465181286400 }]

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
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 1063434857224854979850797056 }, { target := 57, numerator := 15951522858372824697761955840 }, { target := 58, numerator := 28003784573587847802737655808 }, { target := 59, numerator := 1063434857224854979850797056 }, { target := 60, numerator := 17723914287080916330846617600 }, { target := 61, numerator := 1063434857224854979850797056 }, { target := 62, numerator := 28003784573587847802737655808 }, { target := 63, numerator := 27826545430717038639429189632 }, { target := 64, numerator := 17723914287080916330846617600 }, { target := 65, numerator := 429450443175970602696413544448 }, { target := 66, numerator := 27472067144975420312812257280 }, { target := 67, numerator := 15951522858372824697761955840 }, { target := 68, numerator := 28003784573587847802737655808 }, { target := 69, numerator := 1063434857224854979850797056 }, { target := 70, numerator := 27472067144975420312812257280 }, { target := 71, numerator := 1063434857224854979850797056 }, { target := 72, numerator := 28003784573587847802737655808 }, { target := 73, numerator := 28003784573587847802737655808 }, { target := 74, numerator := 1063434857224854979850797056 }, { target := 152, numerator := 42515928283307597268409909248 }, { target := 153, numerator := 637738924249613959026148638720 }, { target := 154, numerator := 1119586111460433394734794276864 }, { target := 155, numerator := 42515928283307597268409909248 }, { target := 156, numerator := 708598804721793287806831820800 }, { target := 157, numerator := 42515928283307597268409909248 }, { target := 158, numerator := 1119586111460433394734794276864 }, { target := 159, numerator := 1112500123413215461856725958656 }, { target := 160, numerator := 708598804721793287806831820800 }, { target := 161, numerator := 17169349038409051363559535017984 }, { target := 162, numerator := 1098328147318779596100589322240 }, { target := 163, numerator := 637738924249613959026148638720 }, { target := 164, numerator := 1119586111460433394734794276864 }, { target := 165, numerator := 42515928283307597268409909248 }, { target := 166, numerator := 1098328147318779596100589322240 }, { target := 167, numerator := 42515928283307597268409909248 }, { target := 168, numerator := 1119586111460433394734794276864 }, { target := 169, numerator := 1119586111460433394734794276864 }, { target := 170, numerator := 42515928283307597268409909248 }, { target := 283, numerator := 42515917893178997751504961536 }, { target := 284, numerator := 637738768397684966272574423040 }, { target := 285, numerator := 1119585837853713607456297320448 }, { target := 286, numerator := 42515917893178997751504961536 }, { target := 287, numerator := 708598631552983295858416025600 }, { target := 288, numerator := 42515917893178997751504961536 }, { target := 289, numerator := 1119585837853713607456297320448 }, { target := 290, numerator := 1112499851538183774497713160192 }, { target := 291, numerator := 708598631552983295858416025600 }, { target := 292, numerator := 17169344842528785258649420300288 }, { target := 293, numerator := 1098327878907124108580544839680 }, { target := 294, numerator := 637738768397684966272574423040 }, { target := 295, numerator := 1119585837853713607456297320448 }, { target := 296, numerator := 42515917893178997751504961536 }, { target := 297, numerator := 1098327878907124108580544839680 }, { target := 298, numerator := 42515917893178997751504961536 }, { target := 299, numerator := 1119585837853713607456297320448 }, { target := 300, numerator := 1119585837853713607456297320448 }, { target := 301, numerator := 42515917893178997751504961536 }]

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
    Slot4.Left12.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left7.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 1495409423826617577049686016 }, { target := 112, numerator := 58329019135868445285203050496 }, { target := 115, numerator := 58328997740988116605538926592 }, { target := 122, numerator := 1495416555453393803604393984 }, { target := 206, numerator := 245068803821049773543045201920 }, { target := 208, numerator := 9559002852278243553135055339520 }, { target := 211, numerator := 9558999346069411040154657751040 }, { target := 218, numerator := 245069972557327277869844398080 }, { target := 257, numerator := 26239635205794410666777378816 }, { target := 260, numerator := 94383187522993844445771726848 }, { target := 262, numerator := 26239643959479568458619813888 }, { target := 302, numerator := 2523078223182609521145146245120 }, { target := 304, numerator := 98413635501052306675680904478720 }, { target := 307, numerator := 98413599403274811896183065149440 }, { target := 314, numerator := 2523090255775107780977759354880 }, { target := 353, numerator := 5204233805480673751646129356800 }, { target := 356, numerator := 18719474235210327151408997990400 }, { target := 358, numerator := 5204235541641404014188193382400 }, { target := 389, numerator := 27694224731684596893232398336 }, { target := 391, numerator := 27694218128867674162754224128 }, { target := 660, numerator := 1063434857224854979850797056 }, { target := 661, numerator := 15951522858372824697761955840 }, { target := 662, numerator := 28003784573587847802737655808 }, { target := 663, numerator := 1063434857224854979850797056 }, { target := 664, numerator := 17723914287080916330846617600 }, { target := 665, numerator := 1063434857224854979850797056 }, { target := 666, numerator := 28003784573587847802737655808 }, { target := 667, numerator := 27826545430717038639429189632 }, { target := 668, numerator := 17723914287080916330846617600 }, { target := 669, numerator := 429450443175970602696413544448 }, { target := 670, numerator := 27472067144975420312812257280 }, { target := 671, numerator := 15951522858372824697761955840 }, { target := 672, numerator := 28003784573587847802737655808 }, { target := 673, numerator := 1063434857224854979850797056 }, { target := 674, numerator := 27472067144975420312812257280 }, { target := 675, numerator := 1063434857224854979850797056 }, { target := 676, numerator := 28003784573587847802737655808 }, { target := 677, numerator := 28003784573587847802737655808 }, { target := 678, numerator := 1063434857224854979850797056 }, { target := 679, numerator := 245068803821049773543045201920 }, { target := 681, numerator := 9559002852278243553135055339520 }, { target := 684, numerator := 9558999346069411040154657751040 }, { target := 691, numerator := 245069972557327277869844398080 }, { target := 695, numerator := 5204233805480673751646129356800 }, { target := 698, numerator := 18719474235210327151408997990400 }, { target := 700, numerator := 5204235541641404014188193382400 }, { target := 731, numerator := 1251728575410368634858227367936 }, { target := 733, numerator := 1251728276975055840956727164928 }, { target := 749, numerator := 19807040628566084398385987584 }, { target := 965, numerator := 19807040628566084398385987584 }, { target := 966, numerator := 1495409423826617577049686016 }, { target := 968, numerator := 58329019135868445285203050496 }, { target := 971, numerator := 58328997740988116605538926592 }, { target := 978, numerator := 1495416555453393803604393984 }, { target := 982, numerator := 26239635205794410666777378816 }, { target := 985, numerator := 94383187522993844445771726848 }, { target := 987, numerator := 26239643959479568458619813888 }, { target := 992, numerator := 27842037181402273240307466240 }, { target := 994, numerator := 27842030543344120475701739520 }, { target := 1010, numerator := 19807040628566084398385987584 }, { target := 1015, numerator := 19807040628566084398385987584 }]

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
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 51038809130166944418225979392 }, { target := 15, numerator := 38279106847625208313669484544 }, { target := 16, numerator := 40405723894715497664428900352 }, { target := 17, numerator := 52102117653712089093605687296 }, { target := 18, numerator := 697530391445614907049088385024 }, { target := 19, numerator := 1219614876506280942660524965888 }, { target := 20, numerator := 37215798324080063638289776640 }, { target := 21, numerator := 697530391445614907049088385024 }, { target := 22, numerator := 39342415371170352989049192448 }, { target := 23, numerator := 40405723894715497664428900352 }, { target := 24, numerator := 40405723894715497664428900352 }, { target := 25, numerator := 39342415371170352989049192448 }, { target := 26, numerator := 1219614876506280942660524965888 }, { target := 27, numerator := 39342415371170352989049192448 }, { target := 28, numerator := 51038809130166944418225979392 }, { target := 29, numerator := 52102117653712089093605687296 }, { target := 56, numerator := 3986376826002385674386276352 }, { target := 57, numerator := 471164147363587418866688458752 }, { target := 59, numerator := 4471253838201528478798731804672 }, { target := 67, numerator := 471164470513459825026357264384 }, { target := 74, numerator := 3986376826002385674386276352 }, { target := 136, numerator := 182943243994147102547156926464 }, { target := 137, numerator := 137207432995610326910367694848 }, { target := 138, numerator := 144830068162033122849832566784 }, { target := 139, numerator := 186754561577358500516889362432 }, { target := 140, numerator := 2500224334586677068144477995008 }, { target := 141, numerator := 4371581267943473471283104055296 }, { target := 142, numerator := 133396115412398928940635258880 }, { target := 143, numerator := 2500224334586677068144477995008 }, { target := 144, numerator := 141018750578821724880100130816 }, { target := 145, numerator := 144830068162033122849832566784 }, { target := 146, numerator := 144830068162033122849832566784 }, { target := 147, numerator := 141018750578821724880100130816 }, { target := 148, numerator := 4371581267943473471283104055296 }, { target := 149, numerator := 141018750578821724880100130816 }, { target := 150, numerator := 182943243994147102547156926464 }, { target := 151, numerator := 186754561577358500516889362432 }, { target := 152, numerator := 156011233623978200726281125888 }, { target := 153, numerator := 18439526185811501286814528831488 }, { target := 155, numerator := 174987427830123158153483117395968 }, { target := 163, numerator := 18439538832636535655994224541696 }, { target := 170, numerator := 156011233623978200726281125888 }, { target := 267, numerator := 51053640921144761330140446720 }, { target := 268, numerator := 38290230690858570997605335040 }, { target := 269, numerator := 40417465729239602719694520320 }, { target := 270, numerator := 52117258440335277191185039360 }, { target := 271, numerator := 697733092588978404845252771840 }, { target := 272, numerator := 1219969294511521692618147758080 }, { target := 273, numerator := 37226613171668055136560742400 }, { target := 274, numerator := 697733092588978404845252771840 }, { target := 275, numerator := 39353848210049086858649927680 }, { target := 276, numerator := 40417465729239602719694520320 }, { target := 277, numerator := 40417465729239602719694520320 }, { target := 278, numerator := 39353848210049086858649927680 }, { target := 279, numerator := 1219969294511521692618147758080 }, { target := 280, numerator := 39353848210049086858649927680 }, { target := 281, numerator := 51053640921144761330140446720 }, { target := 282, numerator := 52117258440335277191185039360 }, { target := 283, numerator := 156011290843603078753290289152 }, { target := 284, numerator := 18439532948803798519222791831552 }, { target := 286, numerator := 174987492009571946715354834665472 }, { target := 294, numerator := 18439545595633471314543702441984 }, { target := 301, numerator := 156011290843603078753290289152 }]

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
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left6.expected,
    Slot12.Left14.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot13.Left4.expected,
    Slot13.Left5.expected,
    Slot13.Left6.expected,
    Slot13.Left7.expected,
    Slot13.Left8.expected,
    Slot13.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 2247385094397963511686758400 }, { target := 112, numerator := 87951325885686778356375224320 }, { target := 115, numerator := 87951325885686778356375224320 }, { target := 122, numerator := 2247385094397963511686758400 }, { target := 206, numerator := 723930741305658566723292364800 }, { target := 208, numerator := 28331000639788920152398013399040 }, { target := 211, numerator := 28331000639788920152398013399040 }, { target := 218, numerator := 723930741305658566723292364800 }, { target := 257, numerator := 34623322986986286985420734464 }, { target := 260, numerator := 128617016667795754360388976640 }, { target := 262, numerator := 34616034814775701708029820928 }, { target := 302, numerator := 7699307867188878736576940605440 }, { target := 304, numerator := 301312105793227205090413234880512 }, { target := 307, numerator := 301312105793227205090413234880512 }, { target := 314, numerator := 7699307867188878736576940605440 }, { target := 353, numerator := 6072605564352775743760762929152 }, { target := 356, numerator := 22558216361291386014750233067520 }, { target := 358, numerator := 6071327287419721208391274594304 }, { target := 389, numerator := 7795152755620396205386760192 }, { target := 391, numerator := 7795154614129861631624085504 }, { target := 656, numerator := 188843861918416695169208287232 }, { target := 658, numerator := 188843906942307293075796393984 }, { target := 660, numerator := 3986434045627263701395439616 }, { target := 661, numerator := 471170910355884651274951458816 }, { target := 663, numerator := 4471318017650317040670449074176 }, { target := 671, numerator := 471171233510395483575835164672 }, { target := 678, numerator := 3986434045627263701395439616 }, { target := 679, numerator := 723932923232934681250973614080 }, { target := 681, numerator := 28331086029425702372571174928384 }, { target := 684, numerator := 28331086029425702372571174928384 }, { target := 691, numerator := 723932923232934681250973614080 }, { target := 695, numerator := 6072606292391192527542056648704 }, { target := 698, numerator := 22558219065772675158215009239040 }, { target := 700, numerator := 6071328015304886689302637969408 }, { target := 731, numerator := 143078771546709852931131179008 }, { target := 733, numerator := 143078805659351331238519504896 }, { target := 745, numerator := 159423446679462296587587289088 }, { target := 747, numerator := 159423484688978460466118393856 }, { target := 872, numerator := 7795152755620396205386760192 }, { target := 874, numerator := 7795154614129861631624085504 }, { target := 947, numerator := 159423446679462296587587289088 }, { target := 949, numerator := 159423484688978460466118393856 }, { target := 961, numerator := 159171990138958412839026425856 }, { target := 963, numerator := 159172028088522658478001487872 }, { target := 966, numerator := 2247385094397963511686758400 }, { target := 968, numerator := 87951325885686778356375224320 }, { target := 971, numerator := 87951325885686778356375224320 }, { target := 978, numerator := 2247385094397963511686758400 }, { target := 982, numerator := 34622594948569503204127014912 }, { target := 985, numerator := 128614312186506610895612805120 }, { target := 987, numerator := 34615306929610220796666445824 }, { target := 992, numerator := 7795152755620396205386760192 }, { target := 994, numerator := 7795154614129861631624085504 }, { target := 1006, numerator := 188843861918416695169208287232 }, { target := 1008, numerator := 188843906942307293075796393984 }, { target := 1011, numerator := 7795152755620396205386760192 }, { target := 1013, numerator := 7795154614129861631624085504 }]

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
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 7795152755620396205386760192 }, { target := 5, numerator := 188843861918416695169208287232 }, { target := 6, numerator := 143078771546709852931131179008 }, { target := 7, numerator := 159423446679462296587587289088 }, { target := 8, numerator := 7795152755620396205386760192 }, { target := 9, numerator := 159423446679462296587587289088 }, { target := 10, numerator := 159171990138958412839026425856 }, { target := 11, numerator := 7795152755620396205386760192 }, { target := 12, numerator := 188843861918416695169208287232 }, { target := 13, numerator := 7795152755620396205386760192 }, { target := 14, numerator := 34623322986986286985420734464 }, { target := 15, numerator := 6072605564352775743760762929152 }, { target := 20, numerator := 6072606292391192527542056648704 }, { target := 28, numerator := 34622594948569503204127014912 }, { target := 56, numerator := 2248839398816253824571801600 }, { target := 57, numerator := 724399203821602694354907955200 }, { target := 59, numerator := 7704290163047715370789565890560 }, { target := 67, numerator := 724401387160824846057650257920 }, { target := 74, numerator := 2248839398816253824571801600 }, { target := 110, numerator := 3984925387143473464055169024 }, { target := 112, numerator := 155954429970738084869471993856 }, { target := 115, numerator := 155954487169529311020265242624 }, { target := 122, numerator := 3984982585934699614848417792 }, { target := 126, numerator := 7795154614129861631624085504 }, { target := 127, numerator := 188843906942307293075796393984 }, { target := 128, numerator := 143078805659351331238519504896 }, { target := 129, numerator := 159423484688978460466118393856 }, { target := 130, numerator := 7795154614129861631624085504 }, { target := 131, numerator := 159423484688978460466118393856 }, { target := 132, numerator := 159172028088522658478001487872 }, { target := 133, numerator := 7795154614129861631624085504 }, { target := 134, numerator := 188843906942307293075796393984 }, { target := 135, numerator := 7795154614129861631624085504 }, { target := 136, numerator := 128617016667795754360388976640 }, { target := 137, numerator := 22558216361291386014750233067520 }, { target := 142, numerator := 22558219065772675158215009239040 }, { target := 150, numerator := 128614312186506610895612805120 }, { target := 152, numerator := 88008240030996756858331463680 }, { target := 153, numerator := 28349333901635202887613111336960 }, { target := 155, numerator := 301507087742618853411222389260288 }, { target := 163, numerator := 28349419346528436865046954377216 }, { target := 170, numerator := 88008240030996756858331463680 }, { target := 206, numerator := 470992596609040327143088717824 }, { target := 208, numerator := 18432812358691234947369120301056 }, { target := 211, numerator := 18432819119221128284917595111424 }, { target := 218, numerator := 470999357138933664691563528192 }, { target := 267, numerator := 34616034814775701708029820928 }, { target := 268, numerator := 6071327287419721208391274594304 }, { target := 273, numerator := 6071328015304886689302637969408 }, { target := 281, numerator := 34615306929610220796666445824 }, { target := 283, numerator := 88008240030996756858331463680 }, { target := 284, numerator := 28349333901635202887613111336960 }, { target := 286, numerator := 301507087742618853411222389260288 }, { target := 294, numerator := 28349419346528436865046954377216 }, { target := 301, numerator := 88008240030996756858331463680 }, { target := 302, numerator := 4469625855737227904074974756864 }, { target := 304, numerator := 174923714949063583000323283746816 }, { target := 307, numerator := 174923779105144649447298998206464 }, { target := 314, numerator := 4469690011818294351050689216512 }, { target := 660, numerator := 2248839398816253824571801600 }, { target := 661, numerator := 724399203821602694354907955200 }, { target := 663, numerator := 7704290163047715370789565890560 }, { target := 671, numerator := 724401387160824846057650257920 }, { target := 678, numerator := 2248839398816253824571801600 }]

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
    Slot17.Left11.expected,
    Slot17.Left18.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left2.expected,
    Slot18.Left3.expected,
    Slot18.Left4.expected,
    Slot18.Left5.expected,
    Slot18.Left6.expected,
    Slot18.Left7.expected,
    Slot18.Left8.expected,
    Slot18.Left9.expected,
    Slot18.Left10.expected,
    Slot18.Left11.expected,
    Slot18.Left12.expected,
    Slot18.Left13.expected,
    Slot18.Left14.expected,
    Slot18.Left15.expected,
    Slot19.Left0.expected,
    Slot20.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 19807040628566084398385987584 }, { target := 1, numerator := 19807040628566084398385987584 }, { target := 2, numerator := 19807040628566084398385987584 }, { target := 3, numerator := 19807040628566084398385987584 }, { target := 4, numerator := 27694224731684596893232398336 }, { target := 6, numerator := 1251728575410368634858227367936 }, { target := 11, numerator := 27842037181402273240307466240 }, { target := 257, numerator := 51371309515379758388377288704 }, { target := 260, numerator := 184135056658604086928571629568 }, { target := 262, numerator := 51386237930403033390923120640 }, { target := 353, numerator := 38528482136534818791282966528 }, { target := 356, numerator := 138101292493953065196428722176 }, { target := 358, numerator := 38539678447802275043192340480 }, { target := 379, numerator := 40668953366342308724132020224 }, { target := 382, numerator := 145773586521394902151785873408 }, { target := 384, numerator := 40680771694902401434480803840 }, { target := 524, numerator := 52441545130283503354801815552 }, { target := 527, numerator := 187971203672325005406250205184 }, { target := 529, numerator := 52456784553953096586567352320 }, { target := 620, numerator := 702074563376856697974489612288 }, { target := 623, numerator := 2516512441000922521357145604096 }, { target := 625, numerator := 702278585048841456342615982080 }, { target := 646, numerator := 1227560250294595476488932294656 }, { target := 649, numerator := 4400060624737893493897326231552 }, { target := 651, numerator := 1227916977211922485403933736960 }, { target := 679, numerator := 470992919641253941237889630208 }, { target := 681, numerator := 18432825000911563314593898954752 }, { target := 684, numerator := 18432831761446093389433728401408 }, { target := 691, numerator := 470999680175784016077719076864 }, { target := 695, numerator := 37458246521631073824858439680 }, { target := 698, numerator := 134265145480232146718750146560 }, { target := 700, numerator := 37469131824252211847548108800 }, { target := 721, numerator := 702074563376856697974489612288 }, { target := 724, numerator := 2516512441000922521357145604096 }, { target := 726, numerator := 702278585048841456342615982080 }, { target := 735, numerator := 39598717751438563757707493376 }, { target := 738, numerator := 141937439507673983674107297792 }, { target := 740, numerator := 39610225071352338238836572160 }, { target := 836, numerator := 40668953366342308724132020224 }, { target := 839, numerator := 145773586521394902151785873408 }, { target := 841, numerator := 40680771694902401434480803840 }, { target := 862, numerator := 40668953366342308724132020224 }, { target := 865, numerator := 145773586521394902151785873408 }, { target := 867, numerator := 40680771694902401434480803840 }, { target := 911, numerator := 39598717751438563757707493376 }, { target := 914, numerator := 141937439507673983674107297792 }, { target := 916, numerator := 39610225071352338238836572160 }, { target := 937, numerator := 1227560250294595476488932294656 }, { target := 940, numerator := 4400060624737893493897326231552 }, { target := 942, numerator := 1227916977211922485403933736960 }, { target := 951, numerator := 39598717751438563757707493376 }, { target := 954, numerator := 141937439507673983674107297792 }, { target := 956, numerator := 39610225071352338238836572160 }, { target := 966, numerator := 3984925387143473464055169024 }, { target := 968, numerator := 155954429970738084869471993856 }, { target := 971, numerator := 155954487169529311020265242624 }, { target := 978, numerator := 3984982585934699614848417792 }, { target := 982, numerator := 51371309515379758388377288704 }, { target := 985, numerator := 184135056658604086928571629568 }, { target := 987, numerator := 51386237930403033390923120640 }, { target := 996, numerator := 52441545130283503354801815552 }, { target := 999, numerator := 187971203672325005406250205184 }, { target := 1001, numerator := 52456784553953096586567352320 }]

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
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot22.Left5.expected,
    Slot22.Left12.expected,
    Slot23.Left0.expected,
    Slot23.Left1.expected,
    Slot23.Left2.expected,
    Slot23.Left3.expected,
    Slot23.Left4.expected,
    Slot23.Left5.expected,
    Slot23.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 26204128256936772763304067072 }, { target := 15, numerator := 5197191540520618712739977625600 }, { target := 20, numerator := 5197191540520618712739977625600 }, { target := 28, numerator := 26204128256936772763304067072 }, { target := 56, numerator := 1491481887585444582756712448 }, { target := 57, numerator := 244425156273259754439846133760 }, { target := 59, numerator := 2516451622465124006972736143360 }, { target := 67, numerator := 244425156273259754439846133760 }, { target := 74, numerator := 1491481887585444582756712448 }, { target := 110, numerator := 1091755359414598121790898176 }, { target := 112, numerator := 43648176706298478687009374208 }, { target := 115, numerator := 43648166039468718064461152256 }, { target := 122, numerator := 1091755359414598121790898176 }, { target := 126, numerator := 27694218128867674162754224128 }, { target := 128, numerator := 1251728276975055840956727164928 }, { target := 133, numerator := 27842030543344120475701739520 }, { target := 136, numerator := 94255470083855828418104918016 }, { target := 137, numerator := 18694143417571341593693965516800 }, { target := 142, numerator := 18694143417571341593693965516800 }, { target := 150, numerator := 94255470083855828418104918016 }, { target := 152, numerator := 58175824075761108593712037888 }, { target := 153, numerator := 9533897132377315795937064386560 }, { target := 155, numerator := 98155162394023935548495925084160 }, { target := 163, numerator := 9533897132377315795937064386560 }, { target := 170, numerator := 58175824075761108593712037888 }, { target := 206, numerator := 16376330391218971826863472640 }, { target := 208, numerator := 654722650594477180305140613120 }, { target := 211, numerator := 654722490592030770966917283840 }, { target := 218, numerator := 16376330391218971826863472640 }, { target := 241, numerator := 28749557797917750540493651968 }, { target := 243, numerator := 1149401986599193272091246854144 }, { target := 246, numerator := 1149401705706009575697477009408 }, { target := 253, numerator := 28749557797917750540493651968 }, { target := 267, numerator := 26204136998776619110231965696 }, { target := 268, numerator := 5197193274332011045292133580800 }, { target := 273, numerator := 5197193274332011045292133580800 }, { target := 281, numerator := 26204136998776619110231965696 }, { target := 283, numerator := 58175802737072192464749592576 }, { target := 284, numerator := 9533893635377173585026214789120 }, { target := 286, numerator := 98155126391053472928629071544320 }, { target := 294, numerator := 9533893635377173585026214789120 }, { target := 301, numerator := 58175802737072192464749592576 }, { target := 302, numerator := 1091755359414598121790898176 }, { target := 304, numerator := 43648176706298478687009374208 }, { target := 307, numerator := 43648166039468718064461152256 }, { target := 314, numerator := 1091755359414598121790898176 }, { target := 337, numerator := 18195922656909968696514969600 }, { target := 339, numerator := 727469611771641311450156236800 }, { target := 342, numerator := 727469433991145301074352537600 }, { target := 349, numerator := 18195922656909968696514969600 }, { target := 363, numerator := 1091755359414598121790898176 }, { target := 365, numerator := 43648176706298478687009374208 }, { target := 368, numerator := 43648166039468718064461152256 }, { target := 375, numerator := 1091755359414598121790898176 }, { target := 473, numerator := 28749557797917750540493651968 }, { target := 475, numerator := 1149401986599193272091246854144 }, { target := 478, numerator := 1149401705706009575697477009408 }, { target := 485, numerator := 28749557797917750540493651968 }, { target := 660, numerator := 1491489000481749959077527552 }, { target := 661, numerator := 244426321939973824743462666240 }, { target := 663, numerator := 2516463623455278213595020656640 }, { target := 671, numerator := 244426321939973824743462666240 }, { target := 678, numerator := 1491489000481749959077527552 }]

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
    Slot23.Left7.expected,
    Slot23.Left8.expected,
    Slot23.Left9.expected,
    Slot23.Left10.expected,
    Slot23.Left11.expected,
    Slot23.Left12.expected,
    Slot23.Left13.expected,
    Slot23.Left14.expected,
    Slot23.Left15.expected,
    Slot23.Left16.expected,
    Slot23.Left17.expected,
    Slot23.Left18.expected,
    Slot24.Left0.expected,
    Slot25.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 19884411881021420665567182848 }, { target := 1, numerator := 19826383441679918465181286400 }, { target := 2, numerator := 19690983749883079997614194688 }, { target := 3, numerator := 19826383441679918465181286400 }, { target := 4, numerator := 1798881405143168355089252352 }, { target := 5, numerator := 44101608642219611286059089920 }, { target := 6, numerator := 32611979022272923082585800704 }, { target := 7, numerator := 36383827129831179310998749184 }, { target := 8, numerator := 1798881405143168355089252352 }, { target := 9, numerator := 36325798697407206138253934592 }, { target := 10, numerator := 36964111454070911038446895104 }, { target := 11, numerator := 1798881405143168355089252352 }, { target := 12, numerator := 44101608642219611286059089920 }, { target := 13, numerator := 1798881405143168355089252352 }, { target := 508, numerator := 28567598571348650853528502272 }, { target := 510, numerator := 1142127290481476858976745291776 }, { target := 513, numerator := 1142127011366098122686733484032 }, { target := 520, numerator := 28567598571348650853528502272 }, { target := 569, numerator := 18195922656909968696514969600 }, { target := 571, numerator := 727469611771641311450156236800 }, { target := 574, numerator := 727469433991145301074352537600 }, { target := 581, numerator := 18195922656909968696514969600 }, { target := 604, numerator := 440887205976928541516557713408 }, { target := 606, numerator := 17626588693226868976437285617664 }, { target := 609, numerator := 17626584385605450645031561986048 }, { target := 616, numerator := 440887205976928541516557713408 }, { target := 630, numerator := 28203680118210451479598202880 }, { target := 632, numerator := 1127577898246044032747742167040 }, { target := 635, numerator := 1127577622686275216665246433280 }, { target := 642, numerator := 28203680118210451479598202880 }, { target := 679, numerator := 16376330391218971826863472640 }, { target := 681, numerator := 654722650594477180305140613120 }, { target := 684, numerator := 654722490592030770966917283840 }, { target := 691, numerator := 16376330391218971826863472640 }, { target := 705, numerator := 28749557797917750540493651968 }, { target := 707, numerator := 1149401986599193272091246854144 }, { target := 710, numerator := 1149401705706009575697477009408 }, { target := 717, numerator := 28749557797917750540493651968 }, { target := 785, numerator := 1091755359414598121790898176 }, { target := 787, numerator := 43648176706298478687009374208 }, { target := 790, numerator := 43648166039468718064461152256 }, { target := 797, numerator := 1091755359414598121790898176 }, { target := 820, numerator := 28203680118210451479598202880 }, { target := 822, numerator := 1127577898246044032747742167040 }, { target := 825, numerator := 1127577622686275216665246433280 }, { target := 832, numerator := 28203680118210451479598202880 }, { target := 846, numerator := 1091755359414598121790898176 }, { target := 848, numerator := 43648176706298478687009374208 }, { target := 851, numerator := 43648166039468718064461152256 }, { target := 858, numerator := 1091755359414598121790898176 }, { target := 895, numerator := 28749557797917750540493651968 }, { target := 897, numerator := 1149401986599193272091246854144 }, { target := 900, numerator := 1149401705706009575697477009408 }, { target := 907, numerator := 28749557797917750540493651968 }, { target := 921, numerator := 28749557797917750540493651968 }, { target := 923, numerator := 1149401986599193272091246854144 }, { target := 926, numerator := 1149401705706009575697477009408 }, { target := 933, numerator := 28749557797917750540493651968 }, { target := 966, numerator := 1091755359414598121790898176 }, { target := 968, numerator := 43648176706298478687009374208 }, { target := 971, numerator := 43648166039468718064461152256 }, { target := 978, numerator := 1091755359414598121790898176 }]

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
    Slot25.Left2.expected,
    Slot26.Left0.expected,
    Slot26.Left3.expected,
    Slot26.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 9006655850554068664028495872 }, { target := 15, numerator := 6707084144029625600872284160 }, { target := 16, numerator := 7090346095117032778064986112 }, { target := 17, numerator := 9198286826097772252624846848 }, { target := 18, numerator := 123218717274601407467453677568 }, { target := 19, numerator := 222866824557327273537556185088 }, { target := 20, numerator := 6707084144029625600872284160 }, { target := 21, numerator := 123218717274601407467453677568 }, { target := 22, numerator := 7281977070660736366661337088 }, { target := 23, numerator := 7281977070660736366661337088 }, { target := 24, numerator := 7090346095117032778064986112 }, { target := 25, numerator := 7090346095117032778064986112 }, { target := 26, numerator := 222866824557327273537556185088 }, { target := 27, numerator := 7090346095117032778064986112 }, { target := 28, numerator := 9006655850554068664028495872 }, { target := 29, numerator := 9198286826097772252624846848 }, { target := 126, numerator := 1798881834029968068836327424 }, { target := 127, numerator := 44101619156863733300503511040 }, { target := 128, numerator := 32611986797575550151161806848 }, { target := 129, numerator := 36383835804412579972915396608 }, { target := 130, numerator := 1798881834029968068836327424 }, { target := 131, numerator := 36325807358153548744888418304 }, { target := 132, numerator := 36964120267002892253185179648 }, { target := 133, numerator := 1798881834029968068836327424 }, { target := 134, numerator := 44101619156863733300503511040 }, { target := 135, numerator := 1798881834029968068836327424 }, { target := 136, numerator := 32896975448992526602390732800 }, { target := 137, numerator := 24497747674781668746461184000 }, { target := 138, numerator := 25897618970483478389116108800 }, { target := 139, numerator := 33596911096843431423718195200 }, { target := 140, numerator := 450058621568131800113558323200 }, { target := 141, numerator := 814025158450602307203838771200 }, { target := 142, numerator := 24497747674781668746461184000 }, { target := 143, numerator := 450058621568131800113558323200 }, { target := 144, numerator := 26597554618334383210443571200 }, { target := 145, numerator := 26597554618334383210443571200 }, { target := 146, numerator := 25897618970483478389116108800 }, { target := 147, numerator := 25897618970483478389116108800 }, { target := 148, numerator := 814025158450602307203838771200 }, { target := 149, numerator := 25897618970483478389116108800 }, { target := 150, numerator := 32896975448992526602390732800 }, { target := 151, numerator := 33596911096843431423718195200 }, { target := 267, numerator := 9006652816064668538807255040 }, { target := 268, numerator := 6707081884303476571452211200 }, { target := 269, numerator := 7090343706263675232678051840 }, { target := 270, numerator := 9198283727044767869420175360 }, { target := 271, numerator := 123218675760203869584107765760 }, { target := 272, numerator := 222866749469855521502826332160 }, { target := 273, numerator := 6707081884303476571452211200 }, { target := 274, numerator := 123218675760203869584107765760 }, { target := 275, numerator := 7281974617243774563290972160 }, { target := 276, numerator := 7281974617243774563290972160 }, { target := 277, numerator := 7090343706263675232678051840 }, { target := 278, numerator := 7090343706263675232678051840 }, { target := 279, numerator := 222866749469855521502826332160 }, { target := 280, numerator := 7090343706263675232678051840 }, { target := 281, numerator := 9006652816064668538807255040 }, { target := 282, numerator := 9198283727044767869420175360 }]

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
    Slot27.Left0.expected,
    Slot27.Left1.expected,
    Slot27.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 68342087740089505532608512 }, { target := 57, numerator := 990960272231297830222823424 }, { target := 58, numerator := 1754113585328963975336951808 }, { target := 59, numerator := 56951739783407921277173760 }, { target := 60, numerator := 1093473403841432088521736192 }, { target := 61, numerator := 56951739783407921277173760 }, { target := 62, numerator := 1742723237372282391081517056 }, { target := 63, numerator := 1822455673069053480869560320 }, { target := 64, numerator := 1093473403841432088521736192 }, { target := 65, numerator := 27917742841826563010070577152 }, { target := 66, numerator := 1788284629199008728103256064 }, { target := 67, numerator := 990960272231297830222823424 }, { target := 68, numerator := 1742723237372282391081517056 }, { target := 69, numerator := 56951739783407921277173760 }, { target := 70, numerator := 1788284629199008728103256064 }, { target := 71, numerator := 56951739783407921277173760 }, { target := 72, numerator := 1742723237372282391081517056 }, { target := 73, numerator := 1822455673069053480869560320 }, { target := 74, numerator := 68342087740089505532608512 }, { target := 91, numerator := 77834044370657492412137472 }, { target := 92, numerator := 1128593643374533639975993344 }, { target := 93, numerator := 1997740472180208971911528448 }, { target := 94, numerator := 64861703642214577010114560 }, { target := 95, numerator := 1245344709930519878594199552 }, { target := 96, numerator := 64861703642214577010114560 }, { target := 97, numerator := 1984768131451766056509505536 }, { target := 98, numerator := 2075574516550866464323665920 }, { target := 99, numerator := 1245344709930519878594199552 }, { target := 100, numerator := 31795207125413585650358157312 }, { target := 101, numerator := 2036657494365537718117597184 }, { target := 102, numerator := 1128593643374533639975993344 }, { target := 103, numerator := 1984768131451766056509505536 }, { target := 104, numerator := 64861703642214577010114560 }, { target := 105, numerator := 2036657494365537718117597184 }, { target := 106, numerator := 64861703642214577010114560 }, { target := 107, numerator := 1984768131451766056509505536 }, { target := 108, numerator := 2075574516550866464323665920 }, { target := 109, numerator := 77834044370657492412137472 }, { target := 152, numerator := 60748522435635116028985344 }, { target := 153, numerator := 880853575316709182420287488 }, { target := 154, numerator := 1559212075847967978077290496 }, { target := 155, numerator := 50623768696362596690821120 }, { target := 156, numerator := 971976358970161856463765504 }, { target := 157, numerator := 50623768696362596690821120 }, { target := 158, numerator := 1549087322108695458739126272 }, { target := 159, numerator := 1619960598283603094106275840 }, { target := 160, numerator := 971976358970161856463765504 }, { target := 161, numerator := 24815771414956944897840513024 }, { target := 162, numerator := 1589586337065785536091783168 }, { target := 163, numerator := 880853575316709182420287488 }, { target := 164, numerator := 1549087322108695458739126272 }, { target := 165, numerator := 50623768696362596690821120 }, { target := 166, numerator := 1589586337065785536091783168 }, { target := 167, numerator := 50623768696362596690821120 }, { target := 168, numerator := 1549087322108695458739126272 }, { target := 169, numerator := 1619960598283603094106275840 }, { target := 170, numerator := 60748522435635116028985344 }]

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
    Slot27.Left3.expected,
    Slot27.Left4.expected,
    Slot27.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 187, numerator := 814409878902733274263584768 }, { target := 188, numerator := 11808943244089632476821979136 }, { target := 189, numerator := 20903186891836820706098675712 }, { target := 190, numerator := 678674899085611061886320640 }, { target := 191, numerator := 13030558062443732388217356288 }, { target := 192, numerator := 678674899085611061886320640 }, { target := 193, numerator := 20767451912019698493721411584 }, { target := 194, numerator := 21717596770739553980362260480 }, { target := 195, numerator := 13030558062443732388217356288 }, { target := 196, numerator := 332686435531766542536674377728 }, { target := 197, numerator := 21310391831288187343230468096 }, { target := 198, numerator := 11808943244089632476821979136 }, { target := 199, numerator := 20767451912019698493721411584 }, { target := 200, numerator := 678674899085611061886320640 }, { target := 201, numerator := 21310391831288187343230468096 }, { target := 202, numerator := 678674899085611061886320640 }, { target := 203, numerator := 20767451912019698493721411584 }, { target := 204, numerator := 21717596770739553980362260480 }, { target := 205, numerator := 814409878902733274263584768 }, { target := 222, numerator := 72138870392316700284420096 }, { target := 223, numerator := 1046013620688592154124091392 }, { target := 224, numerator := 1851564340069461973966782464 }, { target := 225, numerator := 60115725326930583570350080 }, { target := 226, numerator := 1154221926277067204550721536 }, { target := 227, numerator := 60115725326930583570350080 }, { target := 228, numerator := 1839541195004075857252712448 }, { target := 229, numerator := 1923703210461778674251202560 }, { target := 230, numerator := 1154221926277067204550721536 }, { target := 231, numerator := 29468728555261372066185609216 }, { target := 232, numerator := 1887633775265620324108992512 }, { target := 233, numerator := 1046013620688592154124091392 }, { target := 234, numerator := 1839541195004075857252712448 }, { target := 235, numerator := 60115725326930583570350080 }, { target := 236, numerator := 1887633775265620324108992512 }, { target := 237, numerator := 60115725326930583570350080 }, { target := 238, numerator := 1839541195004075857252712448 }, { target := 239, numerator := 1923703210461778674251202560 }, { target := 240, numerator := 72138870392316700284420096 }, { target := 283, numerator := 60748522435635116028985344 }, { target := 284, numerator := 880853575316709182420287488 }, { target := 285, numerator := 1559212075847967978077290496 }, { target := 286, numerator := 50623768696362596690821120 }, { target := 287, numerator := 971976358970161856463765504 }, { target := 288, numerator := 50623768696362596690821120 }, { target := 289, numerator := 1549087322108695458739126272 }, { target := 290, numerator := 1619960598283603094106275840 }, { target := 291, numerator := 971976358970161856463765504 }, { target := 292, numerator := 24815771414956944897840513024 }, { target := 293, numerator := 1589586337065785536091783168 }, { target := 294, numerator := 880853575316709182420287488 }, { target := 295, numerator := 1549087322108695458739126272 }, { target := 296, numerator := 50623768696362596690821120 }, { target := 297, numerator := 1589586337065785536091783168 }, { target := 298, numerator := 50623768696362596690821120 }, { target := 299, numerator := 1549087322108695458739126272 }, { target := 300, numerator := 1619960598283603094106275840 }, { target := 301, numerator := 60748522435635116028985344 }]

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
    Slot27.Left6.expected,
    Slot27.Left7.expected,
    Slot27.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 318, numerator := 72138870392316700284420096 }, { target := 319, numerator := 1046013620688592154124091392 }, { target := 320, numerator := 1851564340069461973966782464 }, { target := 321, numerator := 60115725326930583570350080 }, { target := 322, numerator := 1154221926277067204550721536 }, { target := 323, numerator := 60115725326930583570350080 }, { target := 324, numerator := 1839541195004075857252712448 }, { target := 325, numerator := 1923703210461778674251202560 }, { target := 326, numerator := 1154221926277067204550721536 }, { target := 327, numerator := 29468728555261372066185609216 }, { target := 328, numerator := 1887633775265620324108992512 }, { target := 329, numerator := 1046013620688592154124091392 }, { target := 330, numerator := 1839541195004075857252712448 }, { target := 331, numerator := 60115725326930583570350080 }, { target := 332, numerator := 1887633775265620324108992512 }, { target := 333, numerator := 60115725326930583570350080 }, { target := 334, numerator := 1839541195004075857252712448 }, { target := 335, numerator := 1923703210461778674251202560 }, { target := 336, numerator := 72138870392316700284420096 }, { target := 419, numerator := 70240479066203102908514304 }, { target := 420, numerator := 1018486946459944992173457408 }, { target := 421, numerator := 1802838962699212974651867136 }, { target := 422, numerator := 58533732555169252423761920 }, { target := 423, numerator := 1123847665059249646536228864 }, { target := 424, numerator := 58533732555169252423761920 }, { target := 425, numerator := 1791132216188179124167114752 }, { target := 426, numerator := 1873079441765416077560381440 }, { target := 427, numerator := 1123847665059249646536228864 }, { target := 428, numerator := 28693235698543967538128093184 }, { target := 429, numerator := 1837959202232314526106124288 }, { target := 430, numerator := 1018486946459944992173457408 }, { target := 431, numerator := 1791132216188179124167114752 }, { target := 432, numerator := 58533732555169252423761920 }, { target := 433, numerator := 1837959202232314526106124288 }, { target := 434, numerator := 58533732555169252423761920 }, { target := 435, numerator := 1791132216188179124167114752 }, { target := 436, numerator := 1873079441765416077560381440 }, { target := 437, numerator := 70240479066203102908514304 }, { target := 454, numerator := 2653951073906809131516297216 }, { target := 455, numerator := 38482290571648732406986309632 }, { target := 456, numerator := 68118077563608101042251628544 }, { target := 457, numerator := 2211625894922340942930247680 }, { target := 458, numerator := 42463217182508946104260755456 }, { target := 459, numerator := 2211625894922340942930247680 }, { target := 460, numerator := 67675752384623632853665579008 }, { target := 461, numerator := 70772028637514910173767925760 }, { target := 462, numerator := 42463217182508946104260755456 }, { target := 463, numerator := 1084139013690931530224407412736 }, { target := 464, numerator := 69445053100561505608009777152 }, { target := 465, numerator := 38482290571648732406986309632 }, { target := 466, numerator := 67675752384623632853665579008 }, { target := 467, numerator := 2211625894922340942930247680 }, { target := 468, numerator := 69445053100561505608009777152 }, { target := 469, numerator := 2211625894922340942930247680 }, { target := 470, numerator := 67675752384623632853665579008 }, { target := 471, numerator := 70772028637514910173767925760 }, { target := 472, numerator := 2653951073906809131516297216 }]

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
    Slot27.Left9.expected,
    Slot27.Left10.expected,
    Slot27.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 489, numerator := 70240479066203102908514304 }, { target := 490, numerator := 1018486946459944992173457408 }, { target := 491, numerator := 1802838962699212974651867136 }, { target := 492, numerator := 58533732555169252423761920 }, { target := 493, numerator := 1123847665059249646536228864 }, { target := 494, numerator := 58533732555169252423761920 }, { target := 495, numerator := 1791132216188179124167114752 }, { target := 496, numerator := 1873079441765416077560381440 }, { target := 497, numerator := 1123847665059249646536228864 }, { target := 498, numerator := 28693235698543967538128093184 }, { target := 499, numerator := 1837959202232314526106124288 }, { target := 500, numerator := 1018486946459944992173457408 }, { target := 501, numerator := 1791132216188179124167114752 }, { target := 502, numerator := 58533732555169252423761920 }, { target := 503, numerator := 1837959202232314526106124288 }, { target := 504, numerator := 58533732555169252423761920 }, { target := 505, numerator := 1791132216188179124167114752 }, { target := 506, numerator := 1873079441765416077560381440 }, { target := 507, numerator := 70240479066203102908514304 }, { target := 550, numerator := 814409878902733274263584768 }, { target := 551, numerator := 11808943244089632476821979136 }, { target := 552, numerator := 20903186891836820706098675712 }, { target := 553, numerator := 678674899085611061886320640 }, { target := 554, numerator := 13030558062443732388217356288 }, { target := 555, numerator := 678674899085611061886320640 }, { target := 556, numerator := 20767451912019698493721411584 }, { target := 557, numerator := 21717596770739553980362260480 }, { target := 558, numerator := 13030558062443732388217356288 }, { target := 559, numerator := 332686435531766542536674377728 }, { target := 560, numerator := 21310391831288187343230468096 }, { target := 561, numerator := 11808943244089632476821979136 }, { target := 562, numerator := 20767451912019698493721411584 }, { target := 563, numerator := 678674899085611061886320640 }, { target := 564, numerator := 21310391831288187343230468096 }, { target := 565, numerator := 678674899085611061886320640 }, { target := 566, numerator := 20767451912019698493721411584 }, { target := 567, numerator := 21717596770739553980362260480 }, { target := 568, numerator := 814409878902733274263584768 }, { target := 585, numerator := 2653951073906809131516297216 }, { target := 586, numerator := 38482290571648732406986309632 }, { target := 587, numerator := 68118077563608101042251628544 }, { target := 588, numerator := 2211625894922340942930247680 }, { target := 589, numerator := 42463217182508946104260755456 }, { target := 590, numerator := 2211625894922340942930247680 }, { target := 591, numerator := 67675752384623632853665579008 }, { target := 592, numerator := 70772028637514910173767925760 }, { target := 593, numerator := 42463217182508946104260755456 }, { target := 594, numerator := 1084139013690931530224407412736 }, { target := 595, numerator := 69445053100561505608009777152 }, { target := 596, numerator := 38482290571648732406986309632 }, { target := 597, numerator := 67675752384623632853665579008 }, { target := 598, numerator := 2211625894922340942930247680 }, { target := 599, numerator := 69445053100561505608009777152 }, { target := 600, numerator := 2211625894922340942930247680 }, { target := 601, numerator := 67675752384623632853665579008 }, { target := 602, numerator := 70772028637514910173767925760 }, { target := 603, numerator := 2653951073906809131516297216 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent2
