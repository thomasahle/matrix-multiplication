import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 56; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 66, #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416], #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 110, numerator := 67322056579789662166450176 }, some { target := 111, numerator := 76672342215871559689568256 }, some { target := 112, numerator := 59841828070924144147955712 }, some { target := 113, numerator := 802254507575826807483531264 }, some { target := 114, numerator := 71062170834222421175697408 }, some { target := 115, numerator := 59841828070924144147955712 }, some { target := 116, numerator := 71062170834222421175697408 }, some { target := 117, numerator := 69192113707006041671073792 }, some { target := 118, numerator := 2614339863848498547463815168 }, some { target := 119, numerator := 69192113707006041671073792 }, some { target := 120, numerator := 802254507575826807483531264 }, some { target := 121, numerator := 2614339863848498547463815168 }, some { target := 122, numerator := 67322056579789662166450176 }, some { target := 123, numerator := 69192113707006041671073792 }, some { target := 124, numerator := 69192113707006041671073792 }, some { target := 125, numerator := 76672342215871559689568256 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 976169820406950101413527552 }, some { target := 207, numerator := 1111748962130137615498739712 }, some { target := 208, numerator := 867706507028400090145357824 }, some { target := 209, numerator := 11632690359849488708511203328 }, some { target := 210, numerator := 1030401477096225107047612416 }, some { target := 211, numerator := 867706507028400090145357824 }, some { target := 212, numerator := 1030401477096225107047612416 }, some { target := 213, numerator := 1003285648751587604230569984 }, some { target := 214, numerator := 37907928025803228938225319936 }, some { target := 215, numerator := 1003285648751587604230569984 }, some { target := 216, numerator := 11632690359849488708511203328 }, some { target := 217, numerator := 37907928025803228938225319936 }, some { target := 218, numerator := 976169820406950101413527552 }, some { target := 219, numerator := 1003285648751587604230569984 }, some { target := 220, numerator := 1003285648751587604230569984 }, some { target := 221, numerator := 1111748962130137615498739712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 241, numerator := 1727932785547934662272221184 }, some { target := 242, numerator := 1967923450207370032032251904 }, some { target := 243, numerator := 1535940253820386366464196608 }, some { target := 244, numerator := 20591199027779554725410635776 }, some { target := 245, numerator := 1823929051411708810176233472 }, some { target := 246, numerator := 1535940253820386366464196608 }, some { target := 247, numerator := 1823929051411708810176233472 }, some { target := 248, numerator := 1775930918479821736224227328 }, some { target := 249, numerator := 67101389838778129384904589312 }, some { target := 250, numerator := 1775930918479821736224227328 }, some { target := 251, numerator := 20591199027779554725410635776 }, some { target := 252, numerator := 67101389838778129384904589312 }, some { target := 253, numerator := 1727932785547934662272221184 }, some { target := 254, numerator := 1775930918479821736224227328 }, some { target := 255, numerator := 1775930918479821736224227328 }, some { target := 256, numerator := 1967923450207370032032251904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 56101713816491385138708480 }, some { target := 303, numerator := 63893618513226299741306880 }, some { target := 304, numerator := 49868190059103453456629760 }, some { target := 305, numerator := 668545422979855672902942720 }, some { target := 306, numerator := 59218475695185350979747840 }, some { target := 307, numerator := 49868190059103453456629760 }, some { target := 308, numerator := 59218475695185350979747840 }, some { target := 309, numerator := 57660094755838368059228160 }, some { target := 310, numerator := 2178616553207082122886512640 }, some { target := 311, numerator := 57660094755838368059228160 }, some { target := 312, numerator := 668545422979855672902942720 }, some { target := 313, numerator := 2178616553207082122886512640 }, some { target := 314, numerator := 56101713816491385138708480 }, some { target := 315, numerator := 57660094755838368059228160 }, some { target := 316, numerator := 57660094755838368059228160 }, some { target := 317, numerator := 63893618513226299741306880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 1077152905276634594663202816 }, some { target := 338, numerator := 1226757475453944955033092096 }, some { target := 339, numerator := 957469249134786306367291392 }, some { target := 340, numerator := 12836072121213228919736500224 }, some { target := 341, numerator := 1136994733347558738811158528 }, some { target := 342, numerator := 957469249134786306367291392 }, some { target := 343, numerator := 1136994733347558738811158528 }, some { target := 344, numerator := 1107073819312096666737180672 }, some { target := 345, numerator := 41829437821575976759421042688 }, some { target := 346, numerator := 1107073819312096666737180672 }, some { target := 347, numerator := 12836072121213228919736500224 }, some { target := 348, numerator := 41829437821575976759421042688 }, some { target := 349, numerator := 1077152905276634594663202816 }, some { target := 350, numerator := 1107073819312096666737180672 }, some { target := 351, numerator := 1107073819312096666737180672 }, some { target := 352, numerator := 1226757475453944955033092096 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 363, numerator := 56101713816491385138708480 }, some { target := 364, numerator := 63893618513226299741306880 }, some { target := 365, numerator := 49868190059103453456629760 }, some { target := 366, numerator := 668545422979855672902942720 }, some { target := 367, numerator := 59218475695185350979747840 }, some { target := 368, numerator := 49868190059103453456629760 }, some { target := 369, numerator := 59218475695185350979747840 }, some { target := 370, numerator := 57660094755838368059228160 }, some { target := 371, numerator := 2178616553207082122886512640 }, some { target := 372, numerator := 57660094755838368059228160 }, some { target := 373, numerator := 668545422979855672902942720 }, some { target := 374, numerator := 2178616553207082122886512640 }, some { target := 375, numerator := 56101713816491385138708480 }, some { target := 376, numerator := 57660094755838368059228160 }, some { target := 377, numerator := 57660094755838368059228160 }, some { target := 378, numerator := 63893618513226299741306880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 473, numerator := 1716712442784636385244479488 }, some { target := 474, numerator := 1955144726504724772083990528 }, some { target := 475, numerator := 1525966615808565675772870656 }, some { target := 476, numerator := 20457489943183583590830047232 }, some { target := 477, numerator := 1812085356272671739980283904 }, some { target := 478, numerator := 1525966615808565675772870656 }, some { target := 479, numerator := 1812085356272671739980283904 }, some { target := 480, numerator := 1764398899528654062612381696 }, some { target := 481, numerator := 66665666528136712960327286784 }, some { target := 482, numerator := 1764398899528654062612381696 }, some { target := 483, numerator := 20457489943183583590830047232 }, some { target := 484, numerator := 66665666528136712960327286784 }, some { target := 485, numerator := 1716712442784636385244479488 }, some { target := 486, numerator := 1764398899528654062612381696 }, some { target := 487, numerator := 1764398899528654062612381696 }, some { target := 488, numerator := 1955144726504724772083990528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 1795254842127724324438671360 }, some { target := 509, numerator := 2044595792423241591721820160 }, some { target := 510, numerator := 1595782081891310510612152320 }, some { target := 511, numerator := 21393453535355381532894167040 }, some { target := 512, numerator := 1894991222245931231351930880 }, some { target := 513, numerator := 1595782081891310510612152320 }, some { target := 514, numerator := 1894991222245931231351930880 }, some { target := 515, numerator := 1845123032186827777895301120 }, some { target := 516, numerator := 69715729702626627932368404480 }, some { target := 517, numerator := 1845123032186827777895301120 }, some { target := 518, numerator := 21393453535355381532894167040 }, some { target := 519, numerator := 69715729702626627932368404480 }, some { target := 520, numerator := 1795254842127724324438671360 }, some { target := 521, numerator := 1845123032186827777895301120 }, some { target := 522, numerator := 1845123032186827777895301120 }, some { target := 523, numerator := 2044595792423241591721820160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 569, numerator := 1077152905276634594663202816 }, some { target := 570, numerator := 1226757475453944955033092096 }, some { target := 571, numerator := 957469249134786306367291392 }, some { target := 572, numerator := 12836072121213228919736500224 }, some { target := 573, numerator := 1136994733347558738811158528 }, some { target := 574, numerator := 957469249134786306367291392 }, some { target := 575, numerator := 1136994733347558738811158528 }, some { target := 576, numerator := 1107073819312096666737180672 }, some { target := 577, numerator := 41829437821575976759421042688 }, some { target := 578, numerator := 1107073819312096666737180672 }, some { target := 579, numerator := 12836072121213228919736500224 }, some { target := 580, numerator := 41829437821575976759421042688 }, some { target := 581, numerator := 1077152905276634594663202816 }, some { target := 582, numerator := 1107073819312096666737180672 }, some { target := 583, numerator := 1107073819312096666737180672 }, some { target := 584, numerator := 1226757475453944955033092096 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 604, numerator := 27501060112844076994994896896 }, some { target := 605, numerator := 31320651795183532133188632576 }, some { target := 606, numerator := 24445386766972512884439908352 }, some { target := 607, numerator := 327720966344725250857022521344 }, some { target := 608, numerator := 29028896785779859050272391168 }, some { target := 609, numerator := 24445386766972512884439908352 }, some { target := 610, numerator := 29028896785779859050272391168 }, some { target := 611, numerator := 28264978449311968022633644032 }, some { target := 612, numerator := 1067957834382111656638968496128 }, some { target := 613, numerator := 28264978449311968022633644032 }, some { target := 614, numerator := 327720966344725250857022521344 }, some { target := 615, numerator := 1067957834382111656638968496128 }, some { target := 616, numerator := 27501060112844076994994896896 }, some { target := 617, numerator := 28264978449311968022633644032 }, some { target := 618, numerator := 28264978449311968022633644032 }, some { target := 619, numerator := 31320651795183532133188632576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 630, numerator := 1761593813837829493355446272 }, some { target := 631, numerator := 2006259621315305811877036032 }, some { target := 632, numerator := 1565861167855848438538174464 }, some { target := 633, numerator := 20992326281567468129152401408 }, some { target := 634, numerator := 1859460136828820020764082176 }, some { target := 635, numerator := 1565861167855848438538174464 }, some { target := 636, numerator := 1859460136828820020764082176 }, some { target := 637, numerator := 1810526975333324757059764224 }, some { target := 638, numerator := 68408559770702378658636496896 }, some { target := 639, numerator := 1810526975333324757059764224 }, some { target := 640, numerator := 20992326281567468129152401408 }, some { target := 641, numerator := 68408559770702378658636496896 }, some { target := 642, numerator := 1761593813837829493355446272 }, some { target := 643, numerator := 1810526975333324757059764224 }, some { target := 644, numerator := 1810526975333324757059764224 }, some { target := 645, numerator := 2006259621315305811877036032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 976169820406950101413527552 }, some { target := 680, numerator := 1111748962130137615498739712 }, some { target := 681, numerator := 867706507028400090145357824 }, some { target := 682, numerator := 11632690359849488708511203328 }, some { target := 683, numerator := 1030401477096225107047612416 }, some { target := 684, numerator := 867706507028400090145357824 }, some { target := 685, numerator := 1030401477096225107047612416 }, some { target := 686, numerator := 1003285648751587604230569984 }, some { target := 687, numerator := 37907928025803228938225319936 }, some { target := 688, numerator := 1003285648751587604230569984 }, some { target := 689, numerator := 11632690359849488708511203328 }, some { target := 690, numerator := 37907928025803228938225319936 }, some { target := 691, numerator := 976169820406950101413527552 }, some { target := 692, numerator := 1003285648751587604230569984 }, some { target := 693, numerator := 1003285648751587604230569984 }, some { target := 694, numerator := 1111748962130137615498739712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 705, numerator := 1716712442784636385244479488 }, some { target := 706, numerator := 1955144726504724772083990528 }, some { target := 707, numerator := 1525966615808565675772870656 }, some { target := 708, numerator := 20457489943183583590830047232 }, some { target := 709, numerator := 1812085356272671739980283904 }, some { target := 710, numerator := 1525966615808565675772870656 }, some { target := 711, numerator := 1812085356272671739980283904 }, some { target := 712, numerator := 1764398899528654062612381696 }, some { target := 713, numerator := 66665666528136712960327286784 }, some { target := 714, numerator := 1764398899528654062612381696 }, some { target := 715, numerator := 20457489943183583590830047232 }, some { target := 716, numerator := 66665666528136712960327286784 }, some { target := 717, numerator := 1716712442784636385244479488 }, some { target := 718, numerator := 1764398899528654062612381696 }, some { target := 719, numerator := 1764398899528654062612381696 }, some { target := 720, numerator := 1955144726504724772083990528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 785, numerator := 56101713816491385138708480 }, some { target := 786, numerator := 63893618513226299741306880 }, some { target := 787, numerator := 49868190059103453456629760 }, some { target := 788, numerator := 668545422979855672902942720 }, some { target := 789, numerator := 59218475695185350979747840 }, some { target := 790, numerator := 49868190059103453456629760 }, some { target := 791, numerator := 59218475695185350979747840 }, some { target := 792, numerator := 57660094755838368059228160 }, some { target := 793, numerator := 2178616553207082122886512640 }, some { target := 794, numerator := 57660094755838368059228160 }, some { target := 795, numerator := 668545422979855672902942720 }, some { target := 796, numerator := 2178616553207082122886512640 }, some { target := 797, numerator := 56101713816491385138708480 }, some { target := 798, numerator := 57660094755838368059228160 }, some { target := 799, numerator := 57660094755838368059228160 }, some { target := 800, numerator := 63893618513226299741306880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 820, numerator := 1761593813837829493355446272 }, some { target := 821, numerator := 2006259621315305811877036032 }, some { target := 822, numerator := 1565861167855848438538174464 }, some { target := 823, numerator := 20992326281567468129152401408 }, some { target := 824, numerator := 1859460136828820020764082176 }, some { target := 825, numerator := 1565861167855848438538174464 }, some { target := 826, numerator := 1859460136828820020764082176 }, some { target := 827, numerator := 1810526975333324757059764224 }, some { target := 828, numerator := 68408559770702378658636496896 }, some { target := 829, numerator := 1810526975333324757059764224 }, some { target := 830, numerator := 20992326281567468129152401408 }, some { target := 831, numerator := 68408559770702378658636496896 }, some { target := 832, numerator := 1761593813837829493355446272 }, some { target := 833, numerator := 1810526975333324757059764224 }, some { target := 834, numerator := 1810526975333324757059764224 }, some { target := 835, numerator := 2006259621315305811877036032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 56101713816491385138708480 }, some { target := 847, numerator := 63893618513226299741306880 }, some { target := 848, numerator := 49868190059103453456629760 }, some { target := 849, numerator := 668545422979855672902942720 }, some { target := 850, numerator := 59218475695185350979747840 }, some { target := 851, numerator := 49868190059103453456629760 }, some { target := 852, numerator := 59218475695185350979747840 }, some { target := 853, numerator := 57660094755838368059228160 }, some { target := 854, numerator := 2178616553207082122886512640 }, some { target := 855, numerator := 57660094755838368059228160 }, some { target := 856, numerator := 668545422979855672902942720 }, some { target := 857, numerator := 2178616553207082122886512640 }, some { target := 858, numerator := 56101713816491385138708480 }, some { target := 859, numerator := 57660094755838368059228160 }, some { target := 860, numerator := 57660094755838368059228160 }, some { target := 861, numerator := 63893618513226299741306880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 895, numerator := 1716712442784636385244479488 }, some { target := 896, numerator := 1955144726504724772083990528 }, some { target := 897, numerator := 1525966615808565675772870656 }, some { target := 898, numerator := 20457489943183583590830047232 }, some { target := 899, numerator := 1812085356272671739980283904 }, some { target := 900, numerator := 1525966615808565675772870656 }, some { target := 901, numerator := 1812085356272671739980283904 }, some { target := 902, numerator := 1764398899528654062612381696 }, some { target := 903, numerator := 66665666528136712960327286784 }, some { target := 904, numerator := 1764398899528654062612381696 }, some { target := 905, numerator := 20457489943183583590830047232 }, some { target := 906, numerator := 66665666528136712960327286784 }, some { target := 907, numerator := 1716712442784636385244479488 }, some { target := 908, numerator := 1764398899528654062612381696 }, some { target := 909, numerator := 1764398899528654062612381696 }, some { target := 910, numerator := 1955144726504724772083990528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 921, numerator := 1795254842127724324438671360 }, some { target := 922, numerator := 2044595792423241591721820160 }, some { target := 923, numerator := 1595782081891310510612152320 }, some { target := 924, numerator := 21393453535355381532894167040 }, some { target := 925, numerator := 1894991222245931231351930880 }, some { target := 926, numerator := 1595782081891310510612152320 }, some { target := 927, numerator := 1894991222245931231351930880 }, some { target := 928, numerator := 1845123032186827777895301120 }, some { target := 929, numerator := 69715729702626627932368404480 }, some { target := 930, numerator := 1845123032186827777895301120 }, some { target := 931, numerator := 21393453535355381532894167040 }, some { target := 932, numerator := 69715729702626627932368404480 }, some { target := 933, numerator := 1795254842127724324438671360 }, some { target := 934, numerator := 1845123032186827777895301120 }, some { target := 935, numerator := 1845123032186827777895301120 }, some { target := 936, numerator := 2044595792423241591721820160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 67322056579789662166450176 }, some { target := 967, numerator := 76672342215871559689568256 }, some { target := 968, numerator := 59841828070924144147955712 }, some { target := 969, numerator := 802254507575826807483531264 }, some { target := 970, numerator := 71062170834222421175697408 }, some { target := 971, numerator := 59841828070924144147955712 }, some { target := 972, numerator := 71062170834222421175697408 }, some { target := 973, numerator := 69192113707006041671073792 }, some { target := 974, numerator := 2614339863848498547463815168 }, some { target := 975, numerator := 69192113707006041671073792 }, some { target := 976, numerator := 802254507575826807483531264 }, some { target := 977, numerator := 2614339863848498547463815168 }, some { target := 978, numerator := 67322056579789662166450176 }, some { target := 979, numerator := 69192113707006041671073792 }, some { target := 980, numerator := 69192113707006041671073792 }, some { target := 981, numerator := 76672342215871559689568256 }]

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

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 55, #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0], #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 257, numerator := 8845822710365603152170844160 }, some { target := 260, numerator := 32309529458831945770205184000 }, some { target := 262, numerator := 8845819730063513743471411200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 353, numerator := 6587314784314810857999564800 }, some { target := 356, numerator := 24060287894874853233131520000 }, some { target := 358, numerator := 6587312564940914489819136000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 379, numerator := 6963732771989942907028111360 }, some { target := 382, numerator := 25435161488867701989310464000 }, some { target := 384, numerator := 6963730425794681032094515200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 524, numerator := 9034031704203169176685117440 }, some { target := 527, numerator := 32996966255828370148294656000 }, some { target := 529, numerator := 9034028660490397014609100800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 620, numerator := 121018383037554953762677719040 }, some { target := 623, numerator := 442021860468700875111530496000 }, some { target := 625, numerator := 121018342264485943341534412800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 646, numerator := 218887059833089286510099824640 }, some { target := 649, numerator := 799488994906841551718055936000 }, some { target := 651, numerator := 218886986086465244333133004800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 695, numerator := 6587314784314810857999564800 }, some { target := 698, numerator := 24060287894874853233131520000 }, some { target := 700, numerator := 6587312564940914489819136000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 721, numerator := 121018383037554953762677719040 }, some { target := 724, numerator := 442021860468700875111530496000 }, some { target := 726, numerator := 121018342264485943341534412800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 735, numerator := 7151941765827508931542384640 }, some { target := 738, numerator := 26122598285864126367399936000 }, some { target := 740, numerator := 7151939356221564303232204800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 836, numerator := 7151941765827508931542384640 }, some { target := 839, numerator := 26122598285864126367399936000 }, some { target := 841, numerator := 7151939356221564303232204800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 862, numerator := 6963732771989942907028111360 }, some { target := 865, numerator := 25435161488867701989310464000 }, some { target := 867, numerator := 6963730425794681032094515200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 911, numerator := 6963732771989942907028111360 }, some { target := 914, numerator := 25435161488867701989310464000 }, some { target := 916, numerator := 6963730425794681032094515200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 937, numerator := 218887059833089286510099824640 }, some { target := 940, numerator := 799488994906841551718055936000 }, some { target := 942, numerator := 218886986086465244333133004800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 951, numerator := 6963732771989942907028111360 }, some { target := 954, numerator := 25435161488867701989310464000 }, some { target := 956, numerator := 6963730425794681032094515200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 982, numerator := 8845822710365603152170844160 }, some { target := 985, numerator := 32309529458831945770205184000 }, some { target := 987, numerator := 8845819730063513743471411200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 996, numerator := 9034031704203169176685117440 }, some { target := 999, numerator := 32996966255828370148294656000 }, some { target := 1001, numerator := 9034028660490397014609100800 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent2
