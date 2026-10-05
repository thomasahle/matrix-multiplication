import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 2,
parent 43; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot23

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨23, 58, #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 110, numerator := 65735341441545461374648320 }, some { target := 111, numerator := 64365855161513264262676480 }, some { target := 112, numerator := 50670992361191293142958080 }, some { target := 113, numerator := 1592712543677445241223249920 }, some { target := 114, numerator := 50670992361191293142958080 }, some { target := 115, numerator := 50670992361191293142958080 }, some { target := 116, numerator := 52040478641223490254929920 }, some { target := 117, numerator := 52040478641223490254929920 }, some { target := 118, numerator := 880579678060702742997893120 }, some { target := 119, numerator := 47932019801126898919014400 }, some { target := 120, numerator := 1592712543677445241223249920 }, some { target := 121, numerator := 880579678060702742997893120 }, some { target := 122, numerator := 65735341441545461374648320 }, some { target := 123, numerator := 50670992361191293142958080 }, some { target := 124, numerator := 47932019801126898919014400 }, some { target := 125, numerator := 64365855161513264262676480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 1104353736217963751094091776 }, some { target := 207, numerator := 1081346366713422839612964864 }, some { target := 208, numerator := 851272671668013724801695744 }, some { target := 209, numerator := 26757570733781080052550598656 }, some { target := 210, numerator := 851272671668013724801695744 }, some { target := 211, numerator := 851272671668013724801695744 }, some { target := 212, numerator := 874280041172554636282822656 }, some { target := 213, numerator := 874280041172554636282822656 }, some { target := 214, numerator := 14793738591419806082364604416 }, some { target := 215, numerator := 805257932658931901839441920 }, some { target := 216, numerator := 26757570733781080052550598656 }, some { target := 217, numerator := 14793738591419806082364604416 }, some { target := 218, numerator := 1104353736217963751094091776 }, some { target := 219, numerator := 851272671668013724801695744 }, some { target := 220, numerator := 805257932658931901839441920 }, some { target := 221, numerator := 1081346366713422839612964864 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 241, numerator := 2392766428472254794037198848 }, some { target := 242, numerator := 2342917127879082819161423872 }, some { target := 243, numerator := 1844424121947363070403674112 }, some { target := 244, numerator := 57974736589859006780526297088 }, some { target := 245, numerator := 1844424121947363070403674112 }, some { target := 246, numerator := 1844424121947363070403674112 }, some { target := 247, numerator := 1894273422540535045279449088 }, some { target := 248, numerator := 1894273422540535045279449088 }, some { target := 249, numerator := 32053100281409579845123309568 }, some { target := 250, numerator := 1744725520761019120652124160 }, some { target := 251, numerator := 57974736589859006780526297088 }, some { target := 252, numerator := 32053100281409579845123309568 }, some { target := 253, numerator := 2392766428472254794037198848 }, some { target := 254, numerator := 1844424121947363070403674112 }, some { target := 255, numerator := 1744725520761019120652124160 }, some { target := 256, numerator := 2342917127879082819161423872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 78882409729854553649577984 }, some { target := 303, numerator := 77239026193815917115211776 }, some { target := 304, numerator := 60805190833429551771549696 }, some { target := 305, numerator := 1911255052412934289467899904 }, some { target := 306, numerator := 60805190833429551771549696 }, some { target := 307, numerator := 60805190833429551771549696 }, some { target := 308, numerator := 62448574369468188305915904 }, some { target := 309, numerator := 62448574369468188305915904 }, some { target := 310, numerator := 1056695613672843291597471744 }, some { target := 311, numerator := 57518423761352278702817280 }, some { target := 312, numerator := 1911255052412934289467899904 }, some { target := 313, numerator := 1056695613672843291597471744 }, some { target := 314, numerator := 78882409729854553649577984 }, some { target := 315, numerator := 60805190833429551771549696 }, some { target := 316, numerator := 57518423761352278702817280 }, some { target := 317, numerator := 77239026193815917115211776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 1262118555677672858393247744 }, some { target := 338, numerator := 1235824419101054673843388416 }, some { target := 339, numerator := 972883053334872828344795136 }, some { target := 340, numerator := 30580080838606948631486398464 }, some { target := 341, numerator := 972883053334872828344795136 }, some { target := 342, numerator := 972883053334872828344795136 }, some { target := 343, numerator := 999177189911491012894654464 }, some { target := 344, numerator := 999177189911491012894654464 }, some { target := 345, numerator := 16907129818765492665559547904 }, some { target := 346, numerator := 920294780181636459245076480 }, some { target := 347, numerator := 30580080838606948631486398464 }, some { target := 348, numerator := 16907129818765492665559547904 }, some { target := 349, numerator := 1262118555677672858393247744 }, some { target := 350, numerator := 972883053334872828344795136 }, some { target := 351, numerator := 920294780181636459245076480 }, some { target := 352, numerator := 1235824419101054673843388416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 363, numerator := 92029478018163645924507648 }, some { target := 364, numerator := 90112197226118569967747072 }, some { target := 365, numerator := 70939389305667810400141312 }, some { target := 366, numerator := 2229797561148423337712549888 }, some { target := 367, numerator := 70939389305667810400141312 }, some { target := 368, numerator := 70939389305667810400141312 }, some { target := 369, numerator := 72856670097712886356901888 }, some { target := 370, numerator := 72856670097712886356901888 }, some { target := 371, numerator := 1232811549284983840197050368 }, some { target := 372, numerator := 67104827721577658486620160 }, some { target := 373, numerator := 2229797561148423337712549888 }, some { target := 374, numerator := 1232811549284983840197050368 }, some { target := 375, numerator := 92029478018163645924507648 }, some { target := 376, numerator := 70939389305667810400141312 }, some { target := 377, numerator := 67104827721577658486620160 }, some { target := 378, numerator := 90112197226118569967747072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 473, numerator := 2392766428472254794037198848 }, some { target := 474, numerator := 2342917127879082819161423872 }, some { target := 475, numerator := 1844424121947363070403674112 }, some { target := 476, numerator := 57974736589859006780526297088 }, some { target := 477, numerator := 1844424121947363070403674112 }, some { target := 478, numerator := 1844424121947363070403674112 }, some { target := 479, numerator := 1894273422540535045279449088 }, some { target := 480, numerator := 1894273422540535045279449088 }, some { target := 481, numerator := 32053100281409579845123309568 }, some { target := 482, numerator := 1744725520761019120652124160 }, some { target := 483, numerator := 57974736589859006780526297088 }, some { target := 484, numerator := 32053100281409579845123309568 }, some { target := 485, numerator := 2392766428472254794037198848 }, some { target := 486, numerator := 1844424121947363070403674112 }, some { target := 487, numerator := 1744725520761019120652124160 }, some { target := 488, numerator := 2342917127879082819161423872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 2392766428472254794037198848 }, some { target := 509, numerator := 2342917127879082819161423872 }, some { target := 510, numerator := 1844424121947363070403674112 }, some { target := 511, numerator := 57974736589859006780526297088 }, some { target := 512, numerator := 1844424121947363070403674112 }, some { target := 513, numerator := 1844424121947363070403674112 }, some { target := 514, numerator := 1894273422540535045279449088 }, some { target := 515, numerator := 1894273422540535045279449088 }, some { target := 516, numerator := 32053100281409579845123309568 }, some { target := 517, numerator := 1744725520761019120652124160 }, some { target := 518, numerator := 57974736589859006780526297088 }, some { target := 519, numerator := 32053100281409579845123309568 }, some { target := 520, numerator := 2392766428472254794037198848 }, some { target := 521, numerator := 1844424121947363070403674112 }, some { target := 522, numerator := 1744725520761019120652124160 }, some { target := 523, numerator := 2342917127879082819161423872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 569, numerator := 1262118555677672858393247744 }, some { target := 570, numerator := 1235824419101054673843388416 }, some { target := 571, numerator := 972883053334872828344795136 }, some { target := 572, numerator := 30580080838606948631486398464 }, some { target := 573, numerator := 972883053334872828344795136 }, some { target := 574, numerator := 972883053334872828344795136 }, some { target := 575, numerator := 999177189911491012894654464 }, some { target := 576, numerator := 999177189911491012894654464 }, some { target := 577, numerator := 16907129818765492665559547904 }, some { target := 578, numerator := 920294780181636459245076480 }, some { target := 579, numerator := 30580080838606948631486398464 }, some { target := 580, numerator := 16907129818765492665559547904 }, some { target := 581, numerator := 1262118555677672858393247744 }, some { target := 582, numerator := 972883053334872828344795136 }, some { target := 583, numerator := 920294780181636459245076480 }, some { target := 584, numerator := 1235824419101054673843388416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 604, numerator := 29528315375542221249492025344 }, some { target := 605, numerator := 28913142138551758306794274816 }, some { target := 606, numerator := 22761409768647128879816769536 }, some { target := 607, numerator := 715446474619908402357483864064 }, some { target := 608, numerator := 22761409768647128879816769536 }, some { target := 609, numerator := 22761409768647128879816769536 }, some { target := 610, numerator := 23376583005637591822514520064 }, some { target := 611, numerator := 23376583005637591822514520064 }, some { target := 612, numerator := 395556391384867672154653589504 }, some { target := 613, numerator := 21531063294666202994421268480 }, some { target := 614, numerator := 715446474619908402357483864064 }, some { target := 615, numerator := 395556391384867672154653589504 }, some { target := 616, numerator := 29528315375542221249492025344 }, some { target := 617, numerator := 22761409768647128879816769536 }, some { target := 618, numerator := 21531063294666202994421268480 }, some { target := 619, numerator := 28913142138551758306794274816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 630, numerator := 2366472291895636609487339520 }, some { target := 631, numerator := 2317170785814477513456353280 }, some { target := 632, numerator := 1824155725002886553146490880 }, some { target := 633, numerator := 57337651572388028684036997120 }, some { target := 634, numerator := 1824155725002886553146490880 }, some { target := 635, numerator := 1824155725002886553146490880 }, some { target := 636, numerator := 1873457231084045649177477120 }, some { target := 637, numerator := 1873457231084045649177477120 }, some { target := 638, numerator := 31700868410185298747924152320 }, some { target := 639, numerator := 1725552712840568361084518400 }, some { target := 640, numerator := 57337651572388028684036997120 }, some { target := 641, numerator := 31700868410185298747924152320 }, some { target := 642, numerator := 2366472291895636609487339520 }, some { target := 643, numerator := 1824155725002886553146490880 }, some { target := 644, numerator := 1725552712840568361084518400 }, some { target := 645, numerator := 2317170785814477513456353280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 1104353736217963751094091776 }, some { target := 680, numerator := 1081346366713422839612964864 }, some { target := 681, numerator := 851272671668013724801695744 }, some { target := 682, numerator := 26757570733781080052550598656 }, some { target := 683, numerator := 851272671668013724801695744 }, some { target := 684, numerator := 851272671668013724801695744 }, some { target := 685, numerator := 874280041172554636282822656 }, some { target := 686, numerator := 874280041172554636282822656 }, some { target := 687, numerator := 14793738591419806082364604416 }, some { target := 688, numerator := 805257932658931901839441920 }, some { target := 689, numerator := 26757570733781080052550598656 }, some { target := 690, numerator := 14793738591419806082364604416 }, some { target := 691, numerator := 1104353736217963751094091776 }, some { target := 692, numerator := 851272671668013724801695744 }, some { target := 693, numerator := 805257932658931901839441920 }, some { target := 694, numerator := 1081346366713422839612964864 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 705, numerator := 2392766428472254794037198848 }, some { target := 706, numerator := 2342917127879082819161423872 }, some { target := 707, numerator := 1844424121947363070403674112 }, some { target := 708, numerator := 57974736589859006780526297088 }, some { target := 709, numerator := 1844424121947363070403674112 }, some { target := 710, numerator := 1844424121947363070403674112 }, some { target := 711, numerator := 1894273422540535045279449088 }, some { target := 712, numerator := 1894273422540535045279449088 }, some { target := 713, numerator := 32053100281409579845123309568 }, some { target := 714, numerator := 1744725520761019120652124160 }, some { target := 715, numerator := 57974736589859006780526297088 }, some { target := 716, numerator := 32053100281409579845123309568 }, some { target := 717, numerator := 2392766428472254794037198848 }, some { target := 718, numerator := 1844424121947363070403674112 }, some { target := 719, numerator := 1744725520761019120652124160 }, some { target := 720, numerator := 2342917127879082819161423872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 785, numerator := 92029478018163645924507648 }, some { target := 786, numerator := 90112197226118569967747072 }, some { target := 787, numerator := 70939389305667810400141312 }, some { target := 788, numerator := 2229797561148423337712549888 }, some { target := 789, numerator := 70939389305667810400141312 }, some { target := 790, numerator := 70939389305667810400141312 }, some { target := 791, numerator := 72856670097712886356901888 }, some { target := 792, numerator := 72856670097712886356901888 }, some { target := 793, numerator := 1232811549284983840197050368 }, some { target := 794, numerator := 67104827721577658486620160 }, some { target := 795, numerator := 2229797561148423337712549888 }, some { target := 796, numerator := 1232811549284983840197050368 }, some { target := 797, numerator := 92029478018163645924507648 }, some { target := 798, numerator := 70939389305667810400141312 }, some { target := 799, numerator := 67104827721577658486620160 }, some { target := 800, numerator := 90112197226118569967747072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 820, numerator := 2366472291895636609487339520 }, some { target := 821, numerator := 2317170785814477513456353280 }, some { target := 822, numerator := 1824155725002886553146490880 }, some { target := 823, numerator := 57337651572388028684036997120 }, some { target := 824, numerator := 1824155725002886553146490880 }, some { target := 825, numerator := 1824155725002886553146490880 }, some { target := 826, numerator := 1873457231084045649177477120 }, some { target := 827, numerator := 1873457231084045649177477120 }, some { target := 828, numerator := 31700868410185298747924152320 }, some { target := 829, numerator := 1725552712840568361084518400 }, some { target := 830, numerator := 57337651572388028684036997120 }, some { target := 831, numerator := 31700868410185298747924152320 }, some { target := 832, numerator := 2366472291895636609487339520 }, some { target := 833, numerator := 1824155725002886553146490880 }, some { target := 834, numerator := 1725552712840568361084518400 }, some { target := 835, numerator := 2317170785814477513456353280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 92029478018163645924507648 }, some { target := 847, numerator := 90112197226118569967747072 }, some { target := 848, numerator := 70939389305667810400141312 }, some { target := 849, numerator := 2229797561148423337712549888 }, some { target := 850, numerator := 70939389305667810400141312 }, some { target := 851, numerator := 70939389305667810400141312 }, some { target := 852, numerator := 72856670097712886356901888 }, some { target := 853, numerator := 72856670097712886356901888 }, some { target := 854, numerator := 1232811549284983840197050368 }, some { target := 855, numerator := 67104827721577658486620160 }, some { target := 856, numerator := 2229797561148423337712549888 }, some { target := 857, numerator := 1232811549284983840197050368 }, some { target := 858, numerator := 92029478018163645924507648 }, some { target := 859, numerator := 70939389305667810400141312 }, some { target := 860, numerator := 67104827721577658486620160 }, some { target := 861, numerator := 90112197226118569967747072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 895, numerator := 2392766428472254794037198848 }, some { target := 896, numerator := 2342917127879082819161423872 }, some { target := 897, numerator := 1844424121947363070403674112 }, some { target := 898, numerator := 57974736589859006780526297088 }, some { target := 899, numerator := 1844424121947363070403674112 }, some { target := 900, numerator := 1844424121947363070403674112 }, some { target := 901, numerator := 1894273422540535045279449088 }, some { target := 902, numerator := 1894273422540535045279449088 }, some { target := 903, numerator := 32053100281409579845123309568 }, some { target := 904, numerator := 1744725520761019120652124160 }, some { target := 905, numerator := 57974736589859006780526297088 }, some { target := 906, numerator := 32053100281409579845123309568 }, some { target := 907, numerator := 2392766428472254794037198848 }, some { target := 908, numerator := 1844424121947363070403674112 }, some { target := 909, numerator := 1744725520761019120652124160 }, some { target := 910, numerator := 2342917127879082819161423872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 921, numerator := 2392766428472254794037198848 }, some { target := 922, numerator := 2342917127879082819161423872 }, some { target := 923, numerator := 1844424121947363070403674112 }, some { target := 924, numerator := 57974736589859006780526297088 }, some { target := 925, numerator := 1844424121947363070403674112 }, some { target := 926, numerator := 1844424121947363070403674112 }, some { target := 927, numerator := 1894273422540535045279449088 }, some { target := 928, numerator := 1894273422540535045279449088 }, some { target := 929, numerator := 32053100281409579845123309568 }, some { target := 930, numerator := 1744725520761019120652124160 }, some { target := 931, numerator := 57974736589859006780526297088 }, some { target := 932, numerator := 32053100281409579845123309568 }, some { target := 933, numerator := 2392766428472254794037198848 }, some { target := 934, numerator := 1844424121947363070403674112 }, some { target := 935, numerator := 1744725520761019120652124160 }, some { target := 936, numerator := 2342917127879082819161423872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 78882409729854553649577984 }, some { target := 967, numerator := 77239026193815917115211776 }, some { target := 968, numerator := 60805190833429551771549696 }, some { target := 969, numerator := 1911255052412934289467899904 }, some { target := 970, numerator := 60805190833429551771549696 }, some { target := 971, numerator := 60805190833429551771549696 }, some { target := 972, numerator := 62448574369468188305915904 }, some { target := 973, numerator := 62448574369468188305915904 }, some { target := 974, numerator := 1056695613672843291597471744 }, some { target := 975, numerator := 57518423761352278702817280 }, some { target := 976, numerator := 1911255052412934289467899904 }, some { target := 977, numerator := 1056695613672843291597471744 }, some { target := 978, numerator := 78882409729854553649577984 }, some { target := 979, numerator := 60805190833429551771549696 }, some { target := 980, numerator := 57518423761352278702817280 }, some { target := 981, numerator := 77239026193815917115211776 }]

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

end Slot23

namespace Slot24

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨24, 695, #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2, 5, 12]

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
  [some { target := 56, numerator := 1063305561689799340389826560 }, some { target := 57, numerator := 28354814978394649077062041600 }, some { target := 58, numerator := 27114291823089883179940577280 }, some { target := 59, numerator := 886087968074832783658188800 }, some { target := 60, numerator := 27823162197549749406867128320 }, some { target := 61, numerator := 886087968074832783658188800 }, some { target := 62, numerator := 27114291823089883179940577280 }, some { target := 63, numerator := 15417930644502090435652485120 }, some { target := 64, numerator := 27823162197549749406867128320 }, some { target := 65, numerator := 434360321950283030549244149760 }, some { target := 66, numerator := 17012888987036789446237224960 }, some { target := 67, numerator := 28354814978394649077062041600 }, some { target := 68, numerator := 27114291823089883179940577280 }, some { target := 69, numerator := 886087968074832783658188800 }, some { target := 70, numerator := 17012888987036789446237224960 }, some { target := 71, numerator := 886087968074832783658188800 }, some { target := 72, numerator := 27291509416704849736672215040 }, some { target := 73, numerator := 15417930644502090435652485120 }, some { target := 74, numerator := 1063305561689799340389826560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 39266459780654229927808204800 }, some { target := 153, numerator := 1047105594150779464741552128000 }, some { target := 154, numerator := 1001294724406682863159109222400 }, some { target := 155, numerator := 32722049817211858273173504000 }, some { target := 156, numerator := 1027472364260452349777648025600 }, some { target := 157, numerator := 32722049817211858273173504000 }, some { target := 158, numerator := 1001294724406682863159109222400 }, some { target := 159, numerator := 569363666819486333953218969600 }, some { target := 160, numerator := 1027472364260452349777648025600 }, some { target := 161, numerator := 16040348820397252925509651660800 }, some { target := 162, numerator := 628263356490467678844931276800 }, some { target := 163, numerator := 1047105594150779464741552128000 }, some { target := 164, numerator := 1001294724406682863159109222400 }, some { target := 165, numerator := 32722049817211858273173504000 }, some { target := 166, numerator := 628263356490467678844931276800 }, some { target := 167, numerator := 32722049817211858273173504000 }, some { target := 168, numerator := 1007839134370125234813743923200 }, some { target := 169, numerator := 569363666819486333953218969600 }, some { target := 170, numerator := 39266459780654229927808204800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 39266450165288881506704424960 }, some { target := 284, numerator := 1047105337741036840178784665600 }, some { target := 285, numerator := 1001294479214866478420962836480 }, some { target := 286, numerator := 32722041804407401255587020800 }, some { target := 287, numerator := 1027472112658392399425432453120 }, some { target := 288, numerator := 32722041804407401255587020800 }, some { target := 289, numerator := 1001294479214866478420962836480 }, some { target := 290, numerator := 569363527396688781847214161920 }, some { target := 291, numerator := 1027472112658392399425432453120 }, some { target := 292, numerator := 16040344892520508095488757596160 }, some { target := 293, numerator := 628263202644622104107270799360 }, some { target := 294, numerator := 1047105337741036840178784665600 }, some { target := 295, numerator := 1001294479214866478420962836480 }, some { target := 296, numerator := 32722041804407401255587020800 }, some { target := 297, numerator := 628263202644622104107270799360 }, some { target := 298, numerator := 32722041804407401255587020800 }, some { target := 299, numerator := 1007838887575747958672080240640 }, some { target := 300, numerator := 569363527396688781847214161920 }, some { target := 301, numerator := 39266450165288881506704424960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 1063315177055147761493606400 }, some { target := 661, numerator := 28355071388137273639829504000 }, some { target := 662, numerator := 27114537014906267918086963200 }, some { target := 663, numerator := 886095980879289801244672000 }, some { target := 664, numerator := 27823413799609699759082700800 }, some { target := 665, numerator := 886095980879289801244672000 }, some { target := 666, numerator := 27114537014906267918086963200 }, some { target := 667, numerator := 15418070067299642541657292800 }, some { target := 668, numerator := 27823413799609699759082700800 }, some { target := 669, numerator := 434364249827027860570138214400 }, some { target := 670, numerator := 17013042832882364183897702400 }, some { target := 671, numerator := 28355071388137273639829504000 }, some { target := 672, numerator := 27114537014906267918086963200 }, some { target := 673, numerator := 886095980879289801244672000 }, some { target := 674, numerator := 17013042832882364183897702400 }, some { target := 675, numerator := 886095980879289801244672000 }, some { target := 676, numerator := 27291756211082125878335897600 }, some { target := 677, numerator := 15418070067299642541657292800 }, some { target := 678, numerator := 1063315177055147761493606400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected ++ Left5.expected ++ Left12.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq, Left5.routed_eq, Left12.routed_eq]
  rfl

end Slot24

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 651, #[49931561730048, 0, 0, 181611853250560, 0, 49931561730048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 14, numerator := 78181505057243634296401428480 }, some { target := 15, numerator := 80415262344593452419155755008 }, some { target := 16, numerator := 78181505057243634296401428480 }, some { target := 17, numerator := 69246475907844361805384122368 }, some { target := 18, numerator := 3241181823944586096116527792128 }, some { target := 19, numerator := 882334128503178158487958978560 }, some { target := 20, numerator := 80415262344593452419155755008 }, some { target := 21, numerator := 3241181823944586096116527792128 }, some { target := 22, numerator := 78181505057243634296401428480 }, some { target := 23, numerator := 78181505057243634296401428480 }, some { target := 24, numerator := 67012718620494543682629795840 }, some { target := 25, numerator := 78181505057243634296401428480 }, some { target := 26, numerator := 882334128503178158487958978560 }, some { target := 27, numerator := 67012718620494543682629795840 }, some { target := 28, numerator := 78181505057243634296401428480 }, some { target := 29, numerator := 69246475907844361805384122368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 284362986684221943338080665600 }, some { target := 137, numerator := 292487643446628284576311541760 }, some { target := 138, numerator := 284362986684221943338080665600 }, some { target := 139, numerator := 251864359634596578385157160960 }, some { target := 140, numerator := 11788876962251601136673001308160 }, some { target := 141, numerator := 3209239421150504789101196083200 }, some { target := 142, numerator := 292487643446628284576311541760 }, some { target := 143, numerator := 11788876962251601136673001308160 }, some { target := 144, numerator := 284362986684221943338080665600 }, some { target := 145, numerator := 284362986684221943338080665600 }, some { target := 146, numerator := 243739702872190237146926284800 }, some { target := 147, numerator := 284362986684221943338080665600 }, some { target := 148, numerator := 3209239421150504789101196083200 }, some { target := 149, numerator := 243739702872190237146926284800 }, some { target := 150, numerator := 284362986684221943338080665600 }, some { target := 151, numerator := 251864359634596578385157160960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 78181505057243634296401428480 }, some { target := 268, numerator := 80415262344593452419155755008 }, some { target := 269, numerator := 78181505057243634296401428480 }, some { target := 270, numerator := 69246475907844361805384122368 }, some { target := 271, numerator := 3241181823944586096116527792128 }, some { target := 272, numerator := 882334128503178158487958978560 }, some { target := 273, numerator := 80415262344593452419155755008 }, some { target := 274, numerator := 3241181823944586096116527792128 }, some { target := 275, numerator := 78181505057243634296401428480 }, some { target := 276, numerator := 78181505057243634296401428480 }, some { target := 277, numerator := 67012718620494543682629795840 }, some { target := 278, numerator := 78181505057243634296401428480 }, some { target := 279, numerator := 882334128503178158487958978560 }, some { target := 280, numerator := 67012718620494543682629795840 }, some { target := 281, numerator := 78181505057243634296401428480 }, some { target := 282, numerator := 69246475907844361805384122368 }]

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

end Slot25

namespace Slot26

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨26, 32, #[140737521909760, 0, 140737454800896, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 4, numerator := 7737127090208034089074688000 }, some { target := 5, numerator := 155052026887769003145056747520 }, some { target := 6, numerator := 260276955314598266756472504320 }, some { target := 7, numerator := 249754462471915340395330928640 }, some { target := 8, numerator := 7737127090208034089074688000 }, some { target := 9, numerator := 249754462471915340395330928640 }, some { target := 10, numerator := 166812460064885214960450273280 }, some { target := 11, numerator := 8046612173816355452637675520 }, some { target := 12, numerator := 155052026887769003145056747520 }, some { target := 13, numerator := 7427642006599712725511700480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 7737123400859219347164364800 }, some { target := 127, numerator := 155051952953218755717173870592 }, some { target := 128, numerator := 260276831204904138838609231872 }, some { target := 129, numerator := 249754343379735600526465695744 }, some { target := 130, numerator := 7737123400859219347164364800 }, some { target := 131, numerator := 249754343379735600526465695744 }, some { target := 132, numerator := 166812380522524769124863705088 }, some { target := 133, numerator := 8046608336893588121050939392 }, some { target := 134, numerator := 155051952953218755717173870592 }, some { target := 135, numerator := 7427638464824850573277790208 }]

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

end Slot26

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent1
