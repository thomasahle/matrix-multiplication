import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0

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
    Slot0.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 28220862101628999797047296 }, { target := 72, numerator := 423312931524434996955709440 }, { target := 73, numerator := 743149368676230327988912128 }, { target := 74, numerator := 28220862101628999797047296 }, { target := 75, numerator := 470347701693816663284121600 }, { target := 76, numerator := 28220862101628999797047296 }, { target := 77, numerator := 743149368676230327988912128 }, { target := 78, numerator := 738445891659292161356070912 }, { target := 79, numerator := 470347701693816663284121600 }, { target := 80, numerator := 11396524812041177751374266368 }, { target := 81, numerator := 729038937625415828090388480 }, { target := 82, numerator := 423312931524434996955709440 }, { target := 83, numerator := 743149368676230327988912128 }, { target := 84, numerator := 28220862101628999797047296 }, { target := 85, numerator := 729038937625415828090388480 }, { target := 86, numerator := 28220862101628999797047296 }, { target := 87, numerator := 743149368676230327988912128 }, { target := 88, numerator := 743149368676230327988912128 }, { target := 89, numerator := 28220862101628999797047296 }, { target := 146, numerator := 409202500473620497057185792 }, { target := 147, numerator := 6138037507104307455857786880 }, { target := 148, numerator := 10775665845805339755839225856 }, { target := 149, numerator := 409202500473620497057185792 }, { target := 150, numerator := 6820041674560341617619763200 }, { target := 151, numerator := 409202500473620497057185792 }, { target := 152, numerator := 10775665845805339755839225856 }, { target := 153, numerator := 10707465429059736339663028224 }, { target := 154, numerator := 6820041674560341617619763200 }, { target := 155, numerator := 165249609774597077394926862336 }, { target := 156, numerator := 10571064595568529507310632960 }, { target := 157, numerator := 6138037507104307455857786880 }, { target := 158, numerator := 10775665845805339755839225856 }, { target := 159, numerator := 409202500473620497057185792 }, { target := 160, numerator := 10571064595568529507310632960 }, { target := 161, numerator := 409202500473620497057185792 }, { target := 162, numerator := 10775665845805339755839225856 }, { target := 163, numerator := 10775665845805339755839225856 }, { target := 164, numerator := 409202500473620497057185792 }, { target := 181, numerator := 724335460608477661457547264 }, { target := 182, numerator := 10865031909127164921863208960 }, { target := 183, numerator := 19074167129356578418382077952 }, { target := 184, numerator := 724335460608477661457547264 }, { target := 185, numerator := 12072257676807961024292454400 }, { target := 186, numerator := 724335460608477661457547264 }, { target := 187, numerator := 19074167129356578418382077952 }, { target := 188, numerator := 18953444552588498808139153408 }, { target := 189, numerator := 12072257676807961024292454400 }, { target := 190, numerator := 292510803509056895618606170112 }, { target := 191, numerator := 18711999399052339587653304320 }, { target := 192, numerator := 10865031909127164921863208960 }, { target := 193, numerator := 19074167129356578418382077952 }, { target := 194, numerator := 724335460608477661457547264 }, { target := 195, numerator := 18711999399052339587653304320 }, { target := 196, numerator := 724335460608477661457547264 }, { target := 197, numerator := 19074167129356578418382077952 }, { target := 198, numerator := 19074167129356578418382077952 }, { target := 199, numerator := 724335460608477661457547264 }]

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
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 242, numerator := 23517385084690833164206080 }, { target := 243, numerator := 352760776270362497463091200 }, { target := 244, numerator := 619291140563525273324093440 }, { target := 245, numerator := 23517385084690833164206080 }, { target := 246, numerator := 391956418078180552736768000 }, { target := 247, numerator := 23517385084690833164206080 }, { target := 248, numerator := 619291140563525273324093440 }, { target := 249, numerator := 615371576382743467796725760 }, { target := 250, numerator := 391956418078180552736768000 }, { target := 251, numerator := 9497104010034314792811888640 }, { target := 252, numerator := 607532448021179856741990400 }, { target := 253, numerator := 352760776270362497463091200 }, { target := 254, numerator := 619291140563525273324093440 }, { target := 255, numerator := 23517385084690833164206080 }, { target := 256, numerator := 607532448021179856741990400 }, { target := 257, numerator := 23517385084690833164206080 }, { target := 258, numerator := 619291140563525273324093440 }, { target := 259, numerator := 619291140563525273324093440 }, { target := 260, numerator := 23517385084690833164206080 }, { target := 277, numerator := 451533793626063996752756736 }, { target := 278, numerator := 6773006904390959951291351040 }, { target := 279, numerator := 11890389898819685247822594048 }, { target := 280, numerator := 451533793626063996752756736 }, { target := 281, numerator := 7525563227101066612545945600 }, { target := 282, numerator := 451533793626063996752756736 }, { target := 283, numerator := 11890389898819685247822594048 }, { target := 284, numerator := 11815134266548674581697134592 }, { target := 285, numerator := 7525563227101066612545945600 }, { target := 286, numerator := 182344396992658844021988261888 }, { target := 287, numerator := 11664623002006653249446215680 }, { target := 288, numerator := 6773006904390959951291351040 }, { target := 289, numerator := 11890389898819685247822594048 }, { target := 290, numerator := 451533793626063996752756736 }, { target := 291, numerator := 11664623002006653249446215680 }, { target := 292, numerator := 451533793626063996752756736 }, { target := 293, numerator := 11890389898819685247822594048 }, { target := 294, numerator := 11890389898819685247822594048 }, { target := 295, numerator := 451533793626063996752756736 }, { target := 312, numerator := 23517385084690833164206080 }, { target := 313, numerator := 352760776270362497463091200 }, { target := 314, numerator := 619291140563525273324093440 }, { target := 315, numerator := 23517385084690833164206080 }, { target := 316, numerator := 391956418078180552736768000 }, { target := 317, numerator := 23517385084690833164206080 }, { target := 318, numerator := 619291140563525273324093440 }, { target := 319, numerator := 615371576382743467796725760 }, { target := 320, numerator := 391956418078180552736768000 }, { target := 321, numerator := 9497104010034314792811888640 }, { target := 322, numerator := 607532448021179856741990400 }, { target := 323, numerator := 352760776270362497463091200 }, { target := 324, numerator := 619291140563525273324093440 }, { target := 325, numerator := 23517385084690833164206080 }, { target := 326, numerator := 607532448021179856741990400 }, { target := 327, numerator := 23517385084690833164206080 }, { target := 328, numerator := 619291140563525273324093440 }, { target := 329, numerator := 619291140563525273324093440 }, { target := 330, numerator := 23517385084690833164206080 }]

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
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 413, numerator := 719631983591539494824706048 }, { target := 414, numerator := 10794479753873092422370590720 }, { target := 415, numerator := 18950308901243873363717259264 }, { target := 416, numerator := 719631983591539494824706048 }, { target := 417, numerator := 11993866393192324913745100800 }, { target := 418, numerator := 719631983591539494824706048 }, { target := 419, numerator := 18950308901243873363717259264 }, { target := 420, numerator := 18830370237311950114579808256 }, { target := 421, numerator := 11993866393192324913745100800 }, { target := 422, numerator := 290611382707050032660043792384 }, { target := 423, numerator := 18590492909448103616304906240 }, { target := 424, numerator := 10794479753873092422370590720 }, { target := 425, numerator := 18950308901243873363717259264 }, { target := 426, numerator := 719631983591539494824706048 }, { target := 427, numerator := 18590492909448103616304906240 }, { target := 428, numerator := 719631983591539494824706048 }, { target := 429, numerator := 18950308901243873363717259264 }, { target := 430, numerator := 18950308901243873363717259264 }, { target := 431, numerator := 719631983591539494824706048 }, { target := 448, numerator := 752556322710106661254594560 }, { target := 449, numerator := 11288344840651599918818918400 }, { target := 450, numerator := 19817316498032808746370990080 }, { target := 451, numerator := 752556322710106661254594560 }, { target := 452, numerator := 12542605378501777687576576000 }, { target := 453, numerator := 752556322710106661254594560 }, { target := 454, numerator := 19817316498032808746370990080 }, { target := 455, numerator := 19691890444247790969495224320 }, { target := 456, numerator := 12542605378501777687576576000 }, { target := 457, numerator := 303907328321098073369980436480 }, { target := 458, numerator := 19441038336677755415743692800 }, { target := 459, numerator := 11288344840651599918818918400 }, { target := 460, numerator := 19817316498032808746370990080 }, { target := 461, numerator := 752556322710106661254594560 }, { target := 462, numerator := 19441038336677755415743692800 }, { target := 463, numerator := 752556322710106661254594560 }, { target := 464, numerator := 19817316498032808746370990080 }, { target := 465, numerator := 19817316498032808746370990080 }, { target := 466, numerator := 752556322710106661254594560 }, { target := 509, numerator := 451533793626063996752756736 }, { target := 510, numerator := 6773006904390959951291351040 }, { target := 511, numerator := 11890389898819685247822594048 }, { target := 512, numerator := 451533793626063996752756736 }, { target := 513, numerator := 7525563227101066612545945600 }, { target := 514, numerator := 451533793626063996752756736 }, { target := 515, numerator := 11890389898819685247822594048 }, { target := 516, numerator := 11815134266548674581697134592 }, { target := 517, numerator := 7525563227101066612545945600 }, { target := 518, numerator := 182344396992658844021988261888 }, { target := 519, numerator := 11664623002006653249446215680 }, { target := 520, numerator := 6773006904390959951291351040 }, { target := 521, numerator := 11890389898819685247822594048 }, { target := 522, numerator := 451533793626063996752756736 }, { target := 523, numerator := 11664623002006653249446215680 }, { target := 524, numerator := 451533793626063996752756736 }, { target := 525, numerator := 11890389898819685247822594048 }, { target := 526, numerator := 11890389898819685247822594048 }, { target := 527, numerator := 451533793626063996752756736 }]

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
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 544, numerator := 11528222168515446417093820416 }, { target := 545, numerator := 172923332527731696256407306240 }, { target := 546, numerator := 303576517104240088983470604288 }, { target := 547, numerator := 11528222168515446417093820416 }, { target := 548, numerator := 192137036141924106951563673600 }, { target := 549, numerator := 11528222168515446417093820416 }, { target := 550, numerator := 303576517104240088983470604288 }, { target := 551, numerator := 301655146742820847913954967552 }, { target := 552, numerator := 192137036141924106951563673600 }, { target := 553, numerator := 4655480385718821111436387811328 }, { target := 554, numerator := 297812406019982365774923694080 }, { target := 555, numerator := 172923332527731696256407306240 }, { target := 556, numerator := 303576517104240088983470604288 }, { target := 557, numerator := 11528222168515446417093820416 }, { target := 558, numerator := 297812406019982365774923694080 }, { target := 559, numerator := 11528222168515446417093820416 }, { target := 560, numerator := 303576517104240088983470604288 }, { target := 561, numerator := 303576517104240088983470604288 }, { target := 562, numerator := 11528222168515446417093820416 }, { target := 579, numerator := 738445891659292161356070912 }, { target := 580, numerator := 11076688374889382420341063680 }, { target := 581, numerator := 19445741813694693582376534016 }, { target := 582, numerator := 738445891659292161356070912 }, { target := 583, numerator := 12307431527654869355934515200 }, { target := 584, numerator := 738445891659292161356070912 }, { target := 585, numerator := 19445741813694693582376534016 }, { target := 586, numerator := 19322667498418144888817188864 }, { target := 587, numerator := 12307431527654869355934515200 }, { target := 588, numerator := 298209065915077484494293303296 }, { target := 589, numerator := 19076518867865047501698498560 }, { target := 590, numerator := 11076688374889382420341063680 }, { target := 591, numerator := 19445741813694693582376534016 }, { target := 592, numerator := 738445891659292161356070912 }, { target := 593, numerator := 19076518867865047501698498560 }, { target := 594, numerator := 738445891659292161356070912 }, { target := 595, numerator := 19445741813694693582376534016 }, { target := 596, numerator := 19445741813694693582376534016 }, { target := 597, numerator := 738445891659292161356070912 }, { target := 640, numerator := 409202500473620497057185792 }, { target := 641, numerator := 6138037507104307455857786880 }, { target := 642, numerator := 10775665845805339755839225856 }, { target := 643, numerator := 409202500473620497057185792 }, { target := 644, numerator := 6820041674560341617619763200 }, { target := 645, numerator := 409202500473620497057185792 }, { target := 646, numerator := 10775665845805339755839225856 }, { target := 647, numerator := 10707465429059736339663028224 }, { target := 648, numerator := 6820041674560341617619763200 }, { target := 649, numerator := 165249609774597077394926862336 }, { target := 650, numerator := 10571064595568529507310632960 }, { target := 651, numerator := 6138037507104307455857786880 }, { target := 652, numerator := 10775665845805339755839225856 }, { target := 653, numerator := 409202500473620497057185792 }, { target := 654, numerator := 10571064595568529507310632960 }, { target := 655, numerator := 409202500473620497057185792 }, { target := 656, numerator := 10775665845805339755839225856 }, { target := 657, numerator := 10775665845805339755839225856 }, { target := 658, numerator := 409202500473620497057185792 }]

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
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 675, numerator := 719631983591539494824706048 }, { target := 676, numerator := 10794479753873092422370590720 }, { target := 677, numerator := 18950308901243873363717259264 }, { target := 678, numerator := 719631983591539494824706048 }, { target := 679, numerator := 11993866393192324913745100800 }, { target := 680, numerator := 719631983591539494824706048 }, { target := 681, numerator := 18950308901243873363717259264 }, { target := 682, numerator := 18830370237311950114579808256 }, { target := 683, numerator := 11993866393192324913745100800 }, { target := 684, numerator := 290611382707050032660043792384 }, { target := 685, numerator := 18590492909448103616304906240 }, { target := 686, numerator := 10794479753873092422370590720 }, { target := 687, numerator := 18950308901243873363717259264 }, { target := 688, numerator := 719631983591539494824706048 }, { target := 689, numerator := 18590492909448103616304906240 }, { target := 690, numerator := 719631983591539494824706048 }, { target := 691, numerator := 18950308901243873363717259264 }, { target := 692, numerator := 18950308901243873363717259264 }, { target := 693, numerator := 719631983591539494824706048 }, { target := 776, numerator := 23517385084690833164206080 }, { target := 777, numerator := 352760776270362497463091200 }, { target := 778, numerator := 619291140563525273324093440 }, { target := 779, numerator := 23517385084690833164206080 }, { target := 780, numerator := 391956418078180552736768000 }, { target := 781, numerator := 23517385084690833164206080 }, { target := 782, numerator := 619291140563525273324093440 }, { target := 783, numerator := 615371576382743467796725760 }, { target := 784, numerator := 391956418078180552736768000 }, { target := 785, numerator := 9497104010034314792811888640 }, { target := 786, numerator := 607532448021179856741990400 }, { target := 787, numerator := 352760776270362497463091200 }, { target := 788, numerator := 619291140563525273324093440 }, { target := 789, numerator := 23517385084690833164206080 }, { target := 790, numerator := 607532448021179856741990400 }, { target := 791, numerator := 23517385084690833164206080 }, { target := 792, numerator := 619291140563525273324093440 }, { target := 793, numerator := 619291140563525273324093440 }, { target := 794, numerator := 23517385084690833164206080 }, { target := 811, numerator := 738445891659292161356070912 }, { target := 812, numerator := 11076688374889382420341063680 }, { target := 813, numerator := 19445741813694693582376534016 }, { target := 814, numerator := 738445891659292161356070912 }, { target := 815, numerator := 12307431527654869355934515200 }, { target := 816, numerator := 738445891659292161356070912 }, { target := 817, numerator := 19445741813694693582376534016 }, { target := 818, numerator := 19322667498418144888817188864 }, { target := 819, numerator := 12307431527654869355934515200 }, { target := 820, numerator := 298209065915077484494293303296 }, { target := 821, numerator := 19076518867865047501698498560 }, { target := 822, numerator := 11076688374889382420341063680 }, { target := 823, numerator := 19445741813694693582376534016 }, { target := 824, numerator := 738445891659292161356070912 }, { target := 825, numerator := 19076518867865047501698498560 }, { target := 826, numerator := 738445891659292161356070912 }, { target := 827, numerator := 19445741813694693582376534016 }, { target := 828, numerator := 19445741813694693582376534016 }, { target := 829, numerator := 738445891659292161356070912 }]

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
    Slot0.Left15.expected,
    Slot0.Left16.expected,
    Slot0.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 846, numerator := 23517385084690833164206080 }, { target := 847, numerator := 352760776270362497463091200 }, { target := 848, numerator := 619291140563525273324093440 }, { target := 849, numerator := 23517385084690833164206080 }, { target := 850, numerator := 391956418078180552736768000 }, { target := 851, numerator := 23517385084690833164206080 }, { target := 852, numerator := 619291140563525273324093440 }, { target := 853, numerator := 615371576382743467796725760 }, { target := 854, numerator := 391956418078180552736768000 }, { target := 855, numerator := 9497104010034314792811888640 }, { target := 856, numerator := 607532448021179856741990400 }, { target := 857, numerator := 352760776270362497463091200 }, { target := 858, numerator := 619291140563525273324093440 }, { target := 859, numerator := 23517385084690833164206080 }, { target := 860, numerator := 607532448021179856741990400 }, { target := 861, numerator := 23517385084690833164206080 }, { target := 862, numerator := 619291140563525273324093440 }, { target := 863, numerator := 619291140563525273324093440 }, { target := 864, numerator := 23517385084690833164206080 }, { target := 907, numerator := 719631983591539494824706048 }, { target := 908, numerator := 10794479753873092422370590720 }, { target := 909, numerator := 18950308901243873363717259264 }, { target := 910, numerator := 719631983591539494824706048 }, { target := 911, numerator := 11993866393192324913745100800 }, { target := 912, numerator := 719631983591539494824706048 }, { target := 913, numerator := 18950308901243873363717259264 }, { target := 914, numerator := 18830370237311950114579808256 }, { target := 915, numerator := 11993866393192324913745100800 }, { target := 916, numerator := 290611382707050032660043792384 }, { target := 917, numerator := 18590492909448103616304906240 }, { target := 918, numerator := 10794479753873092422370590720 }, { target := 919, numerator := 18950308901243873363717259264 }, { target := 920, numerator := 719631983591539494824706048 }, { target := 921, numerator := 18590492909448103616304906240 }, { target := 922, numerator := 719631983591539494824706048 }, { target := 923, numerator := 18950308901243873363717259264 }, { target := 924, numerator := 18950308901243873363717259264 }, { target := 925, numerator := 719631983591539494824706048 }, { target := 942, numerator := 752556322710106661254594560 }, { target := 943, numerator := 11288344840651599918818918400 }, { target := 944, numerator := 19817316498032808746370990080 }, { target := 945, numerator := 752556322710106661254594560 }, { target := 946, numerator := 12542605378501777687576576000 }, { target := 947, numerator := 752556322710106661254594560 }, { target := 948, numerator := 19817316498032808746370990080 }, { target := 949, numerator := 19691890444247790969495224320 }, { target := 950, numerator := 12542605378501777687576576000 }, { target := 951, numerator := 303907328321098073369980436480 }, { target := 952, numerator := 19441038336677755415743692800 }, { target := 953, numerator := 11288344840651599918818918400 }, { target := 954, numerator := 19817316498032808746370990080 }, { target := 955, numerator := 752556322710106661254594560 }, { target := 956, numerator := 19441038336677755415743692800 }, { target := 957, numerator := 752556322710106661254594560 }, { target := 958, numerator := 19817316498032808746370990080 }, { target := 959, numerator := 19817316498032808746370990080 }, { target := 960, numerator := 752556322710106661254594560 }]

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
    Slot0.Left18.expected,
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
    Slot1.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 3226914392709147564940722176 }, { target := 202, numerator := 125867035718215657719077011456 }, { target := 205, numerator := 125866989550626927242496704512 }, { target := 212, numerator := 3226929781905391057134157824 }, { target := 296, numerator := 2403021356272769463253729280 }, { target := 298, numerator := 93730771279522298301440327680 }, { target := 301, numerator := 93730736899403030925263503360 }, { target := 308, numerator := 2403032816312525255312670720 }, { target := 331, numerator := 2540336862345499146868228096 }, { target := 333, numerator := 99086815352637858204379774976 }, { target := 336, numerator := 99086779007940346978135703552 }, { target := 343, numerator := 2540348977244669555616251904 }, { target := 467, numerator := 3295572145745512406747971584 }, { target := 469, numerator := 128545057754773437670546735104 }, { target := 472, numerator := 128545010604895585268932804608 }, { target := 479, numerator := 3295587862371463207285948416 }, { target := 563, numerator := 44146935202382593282061369344 }, { target := 565, numerator := 1721968169506652508795032305664 }, { target := 568, numerator := 1721967537894747110998412361728 }, { target := 575, numerator := 44147145739684392547601350656 }, { target := 598, numerator := 79848966781292311021831061504 }, { target := 600, numerator := 3114539628516698083559288602624 }, { target := 603, numerator := 3114538486114449284745184411648 }, { target := 610, numerator := 79849347582041910626532458496 }, { target := 659, numerator := 2403021356272769463253729280 }, { target := 661, numerator := 93730771279522298301440327680 }, { target := 664, numerator := 93730736899403030925263503360 }, { target := 671, numerator := 2403032816312525255312670720 }, { target := 694, numerator := 44146935202382593282061369344 }, { target := 696, numerator := 1721968169506652508795032305664 }, { target := 699, numerator := 1721967537894747110998412361728 }, { target := 706, numerator := 44147145739684392547601350656 }, { target := 720, numerator := 2608994615381863988675477504 }, { target := 722, numerator := 101764837389195638155849498624 }, { target := 725, numerator := 101764800062209005004571803648 }, { target := 732, numerator := 2609007057710741705768042496 }, { target := 830, numerator := 2608994615381863988675477504 }, { target := 832, numerator := 101764837389195638155849498624 }, { target := 835, numerator := 101764800062209005004571803648 }, { target := 842, numerator := 2609007057710741705768042496 }, { target := 865, numerator := 2540336862345499146868228096 }, { target := 867, numerator := 99086815352637858204379774976 }, { target := 870, numerator := 99086779007940346978135703552 }, { target := 877, numerator := 2540348977244669555616251904 }, { target := 1017, numerator := 28220862101628999797047296 }, { target := 1018, numerator := 423312931524434996955709440 }, { target := 1019, numerator := 743149368676230327988912128 }, { target := 1020, numerator := 28220862101628999797047296 }, { target := 1021, numerator := 470347701693816663284121600 }, { target := 1022, numerator := 28220862101628999797047296 }, { target := 1023, numerator := 743149368676230327988912128 }, { target := 1024, numerator := 738445891659292161356070912 }, { target := 1025, numerator := 470347701693816663284121600 }, { target := 1026, numerator := 11396524812041177751374266368 }, { target := 1027, numerator := 729038937625415828090388480 }, { target := 1028, numerator := 423312931524434996955709440 }, { target := 1029, numerator := 743149368676230327988912128 }, { target := 1030, numerator := 28220862101628999797047296 }, { target := 1031, numerator := 729038937625415828090388480 }, { target := 1032, numerator := 28220862101628999797047296 }, { target := 1033, numerator := 743149368676230327988912128 }, { target := 1034, numerator := 743149368676230327988912128 }, { target := 1035, numerator := 28220862101628999797047296 }]

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
    Slot3.Left3.expected,
    Slot4.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 347, numerator := 4606772438760057708608487424 }, { target := 350, numerator := 16570423466376329979989327872 }, { target := 352, numerator := 4606773975604423349535506432 }, { target := 614, numerator := 112940227530891737372337111040 }, { target := 617, numerator := 406242639820839057573931909120 }, { target := 619, numerator := 112940265208366507924096286720 }, { target := 710, numerator := 83516326147843626846386126848 }, { target := 713, numerator := 300405741551725724153354911744 }, { target := 715, numerator := 83516354009344707175450148864 }, { target := 736, numerator := 93175687712985683332178116608 }, { target := 739, numerator := 335150177852192222498493825024 }, { target := 741, numerator := 93175718796902369037379436544 }, { target := 746, numerator := 49711035628570085343111413760 }, { target := 748, numerator := 49711023776537017984724500480 }, { target := 881, numerator := 4606772438760057708608487424 }, { target := 884, numerator := 16570423466376329979989327872 }, { target := 886, numerator := 4606773975604423349535506432 }, { target := 926, numerator := 2540336862345499146868228096 }, { target := 928, numerator := 99086815352637858204379774976 }, { target := 931, numerator := 99086779007940346978135703552 }, { target := 938, numerator := 2540348977244669555616251904 }, { target := 961, numerator := 79848966781292311021831061504 }, { target := 963, numerator := 3114539628516698083559288602624 }, { target := 966, numerator := 3114538486114449284745184411648 }, { target := 973, numerator := 79849347582041910626532458496 }, { target := 977, numerator := 93027082150445036309319778304 }, { target := 980, numerator := 334615648062954276370107072512 }, { target := 982, numerator := 93027113184786097316426678272 }, { target := 987, numerator := 2540336862345499146868228096 }, { target := 989, numerator := 99086815352637858204379774976 }, { target := 992, numerator := 99086779007940346978135703552 }, { target := 999, numerator := 2540348977244669555616251904 }, { target := 1003, numerator := 94661743338392153560761499648 }, { target := 1006, numerator := 340495475744571683782361350144 }, { target := 1008, numerator := 94661774918065086246907019264 }, { target := 1013, numerator := 49565964512922507273043968000 }, { target := 1015, numerator := 49565952695477085052862464000 }, { target := 1036, numerator := 3226914392709147564940722176 }, { target := 1038, numerator := 125867035718215657719077011456 }, { target := 1041, numerator := 125866989550626927242496704512 }, { target := 1048, numerator := 3226929781905391057134157824 }, { target := 1052, numerator := 4606772438760057708608487424 }, { target := 1055, numerator := 16570423466376329979989327872 }, { target := 1057, numerator := 4606773975604423349535506432 }, { target := 1062, numerator := 3295572145745512406747971584 }, { target := 1064, numerator := 128545057754773437670546735104 }, { target := 1067, numerator := 128545010604895585268932804608 }, { target := 1074, numerator := 3295587862371463207285948416 }, { target := 1078, numerator := 112940227530891737372337111040 }, { target := 1081, numerator := 406242639820839057573931909120 }, { target := 1083, numerator := 112940265208366507924096286720 }, { target := 1088, numerator := 49227465243078158442886594560 }, { target := 1090, numerator := 49227453506337241545184378880 }, { target := 1092, numerator := 4606772438760057708608487424 }, { target := 1095, numerator := 16570423466376329979989327872 }, { target := 1097, numerator := 4606773975604423349535506432 }, { target := 1102, numerator := 49565964512922507273043968000 }, { target := 1104, numerator := 49565952695477085052862464000 }, { target := 1106, numerator := 79228162514264337593543950336 }]

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
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 2616814402332266315265343488 }, { target := 30, numerator := 1962610801749199736449007616 }, { target := 31, numerator := 2071644735179710832918396928 }, { target := 32, numerator := 2671331369047521863500038144 }, { target := 33, numerator := 35763130165207639641959694336 }, { target := 34, numerator := 62530960822398113825194770432 }, { target := 35, numerator := 1908093835033944188214312960 }, { target := 36, numerator := 35763130165207639641959694336 }, { target := 37, numerator := 2017127768464455284683702272 }, { target := 38, numerator := 2071644735179710832918396928 }, { target := 39, numerator := 2071644735179710832918396928 }, { target := 40, numerator := 2017127768464455284683702272 }, { target := 41, numerator := 62530960822398113825194770432 }, { target := 42, numerator := 2017127768464455284683702272 }, { target := 43, numerator := 2616814402332266315265343488 }, { target := 44, numerator := 2671331369047521863500038144 }, { target := 104, numerator := 104619754284357443078590562304 }, { target := 105, numerator := 78464815713268082308942921728 }, { target := 106, numerator := 82823972141782975770550861824 }, { target := 107, numerator := 106799332498614889809394532352 }, { target := 108, numerator := 1429803308552885055407404351488 }, { target := 109, numerator := 2499976211753291400232153645056 }, { target := 110, numerator := 76285237499010635578138951680 }, { target := 111, numerator := 1429803308552885055407404351488 }, { target := 112, numerator := 80644393927525529039746891776 }, { target := 113, numerator := 82823972141782975770550861824 }, { target := 114, numerator := 82823972141782975770550861824 }, { target := 115, numerator := 80644393927525529039746891776 }, { target := 116, numerator := 2499976211753291400232153645056 }, { target := 117, numerator := 80644393927525529039746891776 }, { target := 118, numerator := 104619754284357443078590562304 }, { target := 119, numerator := 106799332498614889809394532352 }, { target := 226, numerator := 104619728717170156917152022528 }, { target := 227, numerator := 78464796537877617687864016896 }, { target := 228, numerator := 82823951901093040892745351168 }, { target := 229, numerator := 106799306398777868519592689664 }, { target := 230, numerator := 1429802959134658811201077641216 }, { target := 231, numerator := 2499975600804045207999445204992 }, { target := 232, numerator := 76285218856269906085423349760 }, { target := 233, numerator := 1429802959134658811201077641216 }, { target := 234, numerator := 80644374219485329290304684032 }, { target := 235, numerator := 82823951901093040892745351168 }, { target := 236, numerator := 82823951901093040892745351168 }, { target := 237, numerator := 80644374219485329290304684032 }, { target := 238, numerator := 2499975600804045207999445204992 }, { target := 239, numerator := 80644374219485329290304684032 }, { target := 240, numerator := 104619728717170156917152022528 }, { target := 241, numerator := 106799306398777868519592689664 }, { target := 624, numerator := 2616814402332266315265343488 }, { target := 625, numerator := 1962610801749199736449007616 }, { target := 626, numerator := 2071644735179710832918396928 }, { target := 627, numerator := 2671331369047521863500038144 }, { target := 628, numerator := 35763130165207639641959694336 }, { target := 629, numerator := 62530960822398113825194770432 }, { target := 630, numerator := 1908093835033944188214312960 }, { target := 631, numerator := 35763130165207639641959694336 }, { target := 632, numerator := 2017127768464455284683702272 }, { target := 633, numerator := 2071644735179710832918396928 }, { target := 634, numerator := 2071644735179710832918396928 }, { target := 635, numerator := 2017127768464455284683702272 }, { target := 636, numerator := 62530960822398113825194770432 }, { target := 637, numerator := 2017127768464455284683702272 }, { target := 638, numerator := 2616814402332266315265343488 }, { target := 639, numerator := 2671331369047521863500038144 }]

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
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left7.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 75642969067727875863478272 }, { target := 72, numerator := 8940513298284182977665564672 }, { target := 74, numerator := 84843689028819211274044833792 }, { target := 82, numerator := 8940519430172077572986241024 }, { target := 89, numerator := 75642969067727875863478272 }, { target := 146, numerator := 12396425789175755140906352640 }, { target := 147, numerator := 1465177940332900561172708720640 }, { target := 149, numerator := 13904246590108823760558662615040 }, { target := 157, numerator := 1465178945231229774512133242880 }, { target := 164, numerator := 12396425789175755140906352640 }, { target := 200, numerator := 3008083082298428524540723200 }, { target := 202, numerator := 117721211252103063788700303360 }, { target := 205, numerator := 117721211252103063788700303360 }, { target := 212, numerator := 3008083082298428524540723200 }, { target := 242, numerator := 127626003254201805616227287040 }, { target := 243, numerator := 15084574195909807381117182935040 }, { target := 245, numerator := 143149602210819464296089979453440 }, { target := 253, numerator := 15084584541727191800848507207680 }, { target := 260, numerator := 127626003254201805616227287040 }, { target := 296, numerator := 596607671707836683240079360000 }, { target := 298, numerator := 23348217397665554368485654528000 }, { target := 301, numerator := 23348217397665554368485654528000 }, { target := 308, numerator := 596607671707836683240079360000 }, { target := 347, numerator := 24671934448941565829336530944 }, { target := 350, numerator := 91650088162796782310853181440 }, { target := 352, numerator := 24666741033303796365958053888 }, { target := 640, numerator := 12396425789175755140906352640 }, { target := 641, numerator := 1465177940332900561172708720640 }, { target := 643, numerator := 13904246590108823760558662615040 }, { target := 651, numerator := 1465178945231229774512133242880 }, { target := 658, numerator := 12396425789175755140906352640 }, { target := 659, numerator := 596607671707836683240079360000 }, { target := 661, numerator := 23348217397665554368485654528000 }, { target := 664, numerator := 23348217397665554368485654528000 }, { target := 671, numerator := 596607671707836683240079360000 }, { target := 710, numerator := 1115126552903981067187827769344 }, { target := 713, numerator := 4142417251384599516406024765440 }, { target := 715, numerator := 1114891819965227173026031730688 }, { target := 746, numerator := 49517595668457107408908451840 }, { target := 748, numerator := 49517607474373314583021486080 }, { target := 1013, numerator := 49517595668457107408908451840 }, { target := 1015, numerator := 49517607474373314583021486080 }, { target := 1017, numerator := 75642969067727875863478272 }, { target := 1018, numerator := 8940513298284182977665564672 }, { target := 1020, numerator := 84843689028819211274044833792 }, { target := 1028, numerator := 8940519430172077572986241024 }, { target := 1035, numerator := 75642969067727875863478272 }, { target := 1036, numerator := 3008083082298428524540723200 }, { target := 1038, numerator := 117721211252103063788700303360 }, { target := 1041, numerator := 117721211252103063788700303360 }, { target := 1048, numerator := 3008083082298428524540723200 }, { target := 1052, numerator := 24803616021742544242039848960 }, { target := 1055, numerator := 92139252390336433644738969600 }, { target := 1057, numerator := 24798394887275478844880977920 }, { target := 1088, numerator := 49517595668457107408908451840 }, { target := 1090, numerator := 49517607474373314583021486080 }, { target := 1102, numerator := 49517595668457107408908451840 }, { target := 1104, numerator := 49517607474373314583021486080 }]

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
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 4402166558390484958982438912 }, { target := 6, numerator := 106646035011330780780510052352 }, { target := 7, numerator := 80801057152393094892290572288 }, { target := 8, numerator := 90031406387727982709511815168 }, { target := 9, numerator := 4402166558390484958982438912 }, { target := 10, numerator := 90031406387727982709511815168 }, { target := 11, numerator := 89889401014876676743093026816 }, { target := 12, numerator := 4402166558390484958982438912 }, { target := 13, numerator := 106646035011330780780510052352 }, { target := 14, numerator := 4402166558390484958982438912 }, { target := 29, numerator := 2906861821011925186381873152 }, { target := 30, numerator := 509836253317352641836022235136 }, { target := 35, numerator := 509836314441095119534892777472 }, { target := 43, numerator := 2906800697269447487511330816 }, { target := 71, numerator := 26044163072336285034086400 }, { target := 72, numerator := 8389381208694266339839180800 }, { target := 74, numerator := 89224597127136015456392970240 }, { target := 82, numerator := 8389406494289482200310087680 }, { target := 89, numerator := 26044163072336285034086400 }, { target := 94, numerator := 15779103088800282799771746304 }, { target := 95, numerator := 382261497409322980084792950784 }, { target := 96, numerator := 289622892178301964937745924096 }, { target := 97, numerator := 322708108332238041775977005056 }, { target := 98, numerator := 15779103088800282799771746304 }, { target := 99, numerator := 322708108332238041775977005056 }, { target := 100, numerator := 322199105006792871363081142272 }, { target := 101, numerator := 15779103088800282799771746304 }, { target := 102, numerator := 382261497409322980084792950784 }, { target := 103, numerator := 15779103088800282799771746304 }, { target := 104, numerator := 113763228732516910042173145088 }, { target := 105, numerator := 19953001509401116660516398301184 }, { target := 110, numerator := 19953003901545884676095809159168 }, { target := 118, numerator := 113760836587748894462762287104 }, { target := 146, numerator := 8389381208694266339839180800 }, { target := 147, numerator := 2702398877987016657828682137600 }, { target := 149, numerator := 28741148502744488240970234593280 }, { target := 157, numerator := 2702407023017316360999885864960 }, { target := 164, numerator := 8389381208694266339839180800 }, { target := 216, numerator := 4403445820492331138070609920 }, { target := 217, numerator := 106677026167410989828742840320 }, { target := 218, numerator := 80824537801939884437489582080 }, { target := 219, numerator := 90057569361036707791508602880 }, { target := 220, numerator := 4403445820492331138070609920 }, { target := 221, numerator := 90057569361036707791508602880 }, { target := 222, numerator := 89915522721665987432216002560 }, { target := 223, numerator := 4403445820492331138070609920 }, { target := 224, numerator := 106677026167410989828742840320 }, { target := 225, numerator := 4403445820492331138070609920 }, { target := 226, numerator := 113763270457007652017329405952 }, { target := 227, numerator := 19953008827484789470883307585536 }, { target := 232, numerator := 19953011219630434843965125558272 }, { target := 240, numerator := 113760878311362278935511433216 }, { target := 242, numerator := 89224597127136015456392970240 }, { target := 243, numerator := 28741148502744488240970234593280 }, { target := 245, numerator := 305674200794565461231608302403584 }, { target := 253, numerator := 28741235128566941771082328178688 }, { target := 260, numerator := 89224597127136015456392970240 }, { target := 624, numerator := 2906903545502667161538134016 }, { target := 625, numerator := 509843571401025452202931519488 }, { target := 630, numerator := 509843632525645287404209176576 }, { target := 638, numerator := 2906842420882831960260476928 }]

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
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left6.expected,
    Slot13.Left14.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 49517595668457107408908451840 }, { target := 2, numerator := 49517595668457107408908451840 }, { target := 3, numerator := 49517595668457107408908451840 }, { target := 4, numerator := 49517595668457107408908451840 }, { target := 90, numerator := 49517607474373314583021486080 }, { target := 91, numerator := 49517607474373314583021486080 }, { target := 92, numerator := 49517607474373314583021486080 }, { target := 93, numerator := 49517607474373314583021486080 }, { target := 200, numerator := 2887277573902123957984690176 }, { target := 202, numerator := 112996777720844515075575250944 }, { target := 205, numerator := 112996819164227042234729496576 }, { target := 212, numerator := 2887319017284651117138935808 }, { target := 296, numerator := 506401360369112537415567802368 }, { target := 298, numerator := 19818573202793024440474420641792 }, { target := 301, numerator := 19818580471572957395526057197568 }, { target := 308, numerator := 506408629149045492467204358144 }, { target := 347, numerator := 4509536474448789470177132544 }, { target := 350, numerator := 16163959261697850672936910848 }, { target := 352, numerator := 4510846938065314824365015040 }, { target := 614, numerator := 109247157816485190067839565824 }, { target := 617, numerator := 391584948565647930818568388608 }, { target := 619, numerator := 109278904854421013970907299840 }, { target := 640, numerator := 8389406494289482200310087680 }, { target := 641, numerator := 2702407023017316360999885864960 }, { target := 643, numerator := 28741235128566941771082328178688 }, { target := 651, numerator := 2702415168072165185739886166016 }, { target := 658, numerator := 8389406494289482200310087680 }, { target := 659, numerator := 506401421081049242887400718336 }, { target := 661, numerator := 19818575578821321449211621801984 }, { target := 664, numerator := 19818582847602125850791154548736 }, { target := 671, numerator := 506408689861853644466933465088 }, { target := 710, numerator := 82771814643914877694541561856 }, { target := 713, numerator := 296686865158260549448422653952 }, { target := 715, numerator := 82795867992231101131086888960 }, { target := 736, numerator := 92227294348404274970719420416 }, { target := 739, numerator := 330579037803756042794903273472 }, { target := 741, numerator := 92254095443013212859594178560 }, { target := 881, numerator := 4509536474448789470177132544 }, { target := 884, numerator := 16163959261697850672936910848 }, { target := 886, numerator := 4510846938065314824365015040 }, { target := 977, numerator := 92227294348404274970719420416 }, { target := 980, numerator := 330579037803756042794903273472 }, { target := 982, numerator := 92254095443013212859594178560 }, { target := 1003, numerator := 92081825429873668858778222592 }, { target := 1006, numerator := 330057619763056112128034340864 }, { target := 1008, numerator := 92108584251462718833001758720 }, { target := 1017, numerator := 26044163072336285034086400 }, { target := 1018, numerator := 8389381208694266339839180800 }, { target := 1020, numerator := 89224597127136015456392970240 }, { target := 1028, numerator := 8389406494289482200310087680 }, { target := 1035, numerator := 26044163072336285034086400 }, { target := 1036, numerator := 2887216861965418486151774208 }, { target := 1038, numerator := 112994401692547506338374090752 }, { target := 1041, numerator := 112994443135058586969632145408 }, { target := 1048, numerator := 2887258304476499117409828864 }, { target := 1052, numerator := 4509536474448789470177132544 }, { target := 1055, numerator := 16163959261697850672936910848 }, { target := 1057, numerator := 4510846938065314824365015040 }, { target := 1078, numerator := 109247157816485190067839565824 }, { target := 1081, numerator := 391584948565647930818568388608 }, { target := 1083, numerator := 109278904854421013970907299840 }, { target := 1092, numerator := 4509536474448789470177132544 }, { target := 1095, numerator := 16163959261697850672936910848 }, { target := 1097, numerator := 4510846938065314824365015040 }]

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
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left3.expected,
    Slot18.Left11.expected,
    Slot18.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 24671934448941565829336530944 }, { target := 7, numerator := 1115126552903981067187827769344 }, { target := 12, numerator := 24803616021742544242039848960 }, { target := 29, numerator := 3010558870843530111803719680 }, { target := 30, numerator := 597098706828583873925873664000 }, { target := 35, numerator := 597098706828583873925873664000 }, { target := 43, numerator := 3010558870843530111803719680 }, { target := 71, numerator := 75671851453778936526274560 }, { target := 72, numerator := 12401159055991018888573747200 }, { target := 74, numerator := 127674734068731855942923059200 }, { target := 82, numerator := 12401159055991018888573747200 }, { target := 89, numerator := 75671851453778936526274560 }, { target := 94, numerator := 91650088162796782310853181440 }, { target := 96, numerator := 4142417251384599516406024765440 }, { target := 101, numerator := 92139252390336433644738969600 }, { target := 104, numerator := 117818101137907263841201291264 }, { target := 105, numerator := 23367434037499023960558482227200 }, { target := 110, numerator := 23367434037499023960558482227200 }, { target := 118, numerator := 117818101137907263841201291264 }, { target := 146, numerator := 8943927010883756930692546560 }, { target := 147, numerator := 1465737382081786739317486387200 }, { target := 149, numerator := 15090333865324053202950370099200 }, { target := 157, numerator := 1465737382081786739317486387200 }, { target := 164, numerator := 8943927010883756930692546560 }, { target := 200, numerator := 2537516996200985517833060352 }, { target := 202, numerator := 101449458699982975106512060416 }, { target := 205, numerator := 101449433907558940040874688512 }, { target := 212, numerator := 2537516996200985517833060352 }, { target := 216, numerator := 24666741033303796365958053888 }, { target := 218, numerator := 1114891819965227173026031730688 }, { target := 223, numerator := 24798394887275478844880977920 }, { target := 226, numerator := 117818101137907263841201291264 }, { target := 227, numerator := 23367434037499023960558482227200 }, { target := 232, numerator := 23367434037499023960558482227200 }, { target := 240, numerator := 117818101137907263841201291264 }, { target := 242, numerator := 84876084480911162099273564160 }, { target := 243, numerator := 13909555580788514033090376499200 }, { target := 245, numerator := 143204260325447497692155687731200 }, { target := 253, numerator := 13909555580788514033090376499200 }, { target := 260, numerator := 84876084480911162099273564160 }, { target := 296, numerator := 1903137747150739138374795264 }, { target := 298, numerator := 76087094024987231329884045312 }, { target := 301, numerator := 76087075430669205030656016384 }, { target := 308, numerator := 1903137747150739138374795264 }, { target := 331, numerator := 2008867621992446868284506112 }, { target := 333, numerator := 80314154804153188625988714496 }, { target := 336, numerator := 80314135176817494199025795072 }, { target := 343, numerator := 2008867621992446868284506112 }, { target := 624, numerator := 3010558870843530111803719680 }, { target := 625, numerator := 597098706828583873925873664000 }, { target := 630, numerator := 597098706828583873925873664000 }, { target := 638, numerator := 3010558870843530111803719680 }, { target := 640, numerator := 8943933145112960382292459520 }, { target := 641, numerator := 1465738387363811381909808742400 }, { target := 643, numerator := 15090344215091730629332985446400 }, { target := 651, numerator := 1465738387363811381909808742400 }, { target := 658, numerator := 8943933145112960382292459520 }, { target := 1017, numerator := 75671851453778936526274560 }, { target := 1018, numerator := 12401159055991018888573747200 }, { target := 1020, numerator := 127674734068731855942923059200 }, { target := 1028, numerator := 12401159055991018888573747200 }, { target := 1035, numerator := 75671851453778936526274560 }]

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
    Slot19.Left3.expected,
    Slot19.Left4.expected,
    Slot19.Left5.expected,
    Slot19.Left6.expected,
    Slot19.Left7.expected,
    Slot19.Left8.expected,
    Slot19.Left9.expected,
    Slot19.Left10.expected,
    Slot19.Left11.expected,
    Slot19.Left12.expected,
    Slot19.Left13.expected,
    Slot19.Left14.expected,
    Slot19.Left15.expected,
    Slot20.Left0.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 79228162514264337593543950336 }, { target := 1, numerator := 49711035628570085343111413760 }, { target := 2, numerator := 49565964512922507273043968000 }, { target := 3, numerator := 49227465243078158442886594560 }, { target := 4, numerator := 49565964512922507273043968000 }, { target := 90, numerator := 49711023776537017984724500480 }, { target := 91, numerator := 49565952695477085052862464000 }, { target := 92, numerator := 49227453506337241545184378880 }, { target := 93, numerator := 49565952695477085052862464000 }, { target := 467, numerator := 2590381933621839382787915776 }, { target := 469, numerator := 103562989089565953754564395008 }, { target := 472, numerator := 103562963780633084625059577856 }, { target := 479, numerator := 2590381933621839382787915776 }, { target := 563, numerator := 34679398948080135410385158144 }, { target := 565, numerator := 1386475935566433993122331492352 }, { target := 568, numerator := 1386475596736638847225287409664 }, { target := 575, numerator := 34679398948080135410385158144 }, { target := 598, numerator := 60636083221719383103219171328 }, { target := 600, numerator := 2424219356851676509316027777024 }, { target := 603, numerator := 2424218764416043838060068077568 }, { target := 610, numerator := 60636083221719383103219171328 }, { target := 659, numerator := 1850272809729885273419939840 }, { target := 661, numerator := 73973563635404252681831710720 }, { target := 664, numerator := 73973545557595060446471127040 }, { target := 671, numerator := 1850272809729885273419939840 }, { target := 694, numerator := 34679398948080135410385158144 }, { target := 696, numerator := 1386475935566433993122331492352 }, { target := 699, numerator := 1386475596736638847225287409664 }, { target := 706, numerator := 34679398948080135410385158144 }, { target := 720, numerator := 1956002684571593003329650688 }, { target := 722, numerator := 78200624414570209977936379904 }, { target := 725, numerator := 78200605303743349614840905728 }, { target := 732, numerator := 1956002684571593003329650688 }, { target := 830, numerator := 2008867621992446868284506112 }, { target := 832, numerator := 80314154804153188625988714496 }, { target := 835, numerator := 80314135176817494199025795072 }, { target := 842, numerator := 2008867621992446868284506112 }, { target := 865, numerator := 2008867621992446868284506112 }, { target := 867, numerator := 80314154804153188625988714496 }, { target := 870, numerator := 80314135176817494199025795072 }, { target := 877, numerator := 2008867621992446868284506112 }, { target := 926, numerator := 1956002684571593003329650688 }, { target := 928, numerator := 78200624414570209977936379904 }, { target := 931, numerator := 78200605303743349614840905728 }, { target := 938, numerator := 1956002684571593003329650688 }, { target := 961, numerator := 60636083221719383103219171328 }, { target := 963, numerator := 2424219356851676509316027777024 }, { target := 966, numerator := 2424218764416043838060068077568 }, { target := 973, numerator := 60636083221719383103219171328 }, { target := 987, numerator := 1956002684571593003329650688 }, { target := 989, numerator := 78200624414570209977936379904 }, { target := 992, numerator := 78200605303743349614840905728 }, { target := 999, numerator := 1956002684571593003329650688 }, { target := 1036, numerator := 2537516996200985517833060352 }, { target := 1038, numerator := 101449458699982975106512060416 }, { target := 1041, numerator := 101449433907558940040874688512 }, { target := 1048, numerator := 2537516996200985517833060352 }, { target := 1062, numerator := 2590381933621839382787915776 }, { target := 1064, numerator := 103562989089565953754564395008 }, { target := 1067, numerator := 103562963780633084625059577856 }, { target := 1074, numerator := 2590381933621839382787915776 }]

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
    Slot22.Left0.expected,
    Slot22.Left3.expected,
    Slot22.Left5.expected,
    Slot23.Left0.expected,
    Slot23.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 4606772438760057708608487424 }, { target := 6, numerator := 112940227530891737372337111040 }, { target := 7, numerator := 83516326147843626846386126848 }, { target := 8, numerator := 93175687712985683332178116608 }, { target := 9, numerator := 4606772438760057708608487424 }, { target := 10, numerator := 93027082150445036309319778304 }, { target := 11, numerator := 94661743338392153560761499648 }, { target := 12, numerator := 4606772438760057708608487424 }, { target := 13, numerator := 112940227530891737372337111040 }, { target := 14, numerator := 4606772438760057708608487424 }, { target := 29, numerator := 3158740144975855714977185792 }, { target := 30, numerator := 2352253299450105319663861760 }, { target := 31, numerator := 2486667773704397052216082432 }, { target := 32, numerator := 3225947382103001581253296128 }, { target := 33, numerator := 43214253472754792015538946048 }, { target := 34, numerator := 78162016778870642479116320768 }, { target := 35, numerator := 2352253299450105319663861760 }, { target := 36, numerator := 43214253472754792015538946048 }, { target := 37, numerator := 2553875010831542918492192768 }, { target := 38, numerator := 2553875010831542918492192768 }, { target := 39, numerator := 2486667773704397052216082432 }, { target := 40, numerator := 2486667773704397052216082432 }, { target := 41, numerator := 78162016778870642479116320768 }, { target := 42, numerator := 2486667773704397052216082432 }, { target := 43, numerator := 3158740144975855714977185792 }, { target := 44, numerator := 3225947382103001581253296128 }, { target := 94, numerator := 16570423466376329979989327872 }, { target := 95, numerator := 406242639820839057573931909120 }, { target := 96, numerator := 300405741551725724153354911744 }, { target := 97, numerator := 335150177852192222498493825024 }, { target := 98, numerator := 16570423466376329979989327872 }, { target := 99, numerator := 334615648062954276370107072512 }, { target := 100, numerator := 340495475744571683782361350144 }, { target := 101, numerator := 16570423466376329979989327872 }, { target := 102, numerator := 406242639820839057573931909120 }, { target := 103, numerator := 16570423466376329979989327872 }, { target := 104, numerator := 123207872991774481851772567552 }, { target := 105, numerator := 91750543717278869464085954560 }, { target := 106, numerator := 96993431929694804862033723392 }, { target := 107, numerator := 125829317097982449550746451968 }, { target := 108, numerator := 1685588560291723230440207679488 }, { target := 109, numerator := 3048739495519866433906627575808 }, { target := 110, numerator := 91750543717278869464085954560 }, { target := 111, numerator := 1685588560291723230440207679488 }, { target := 112, numerator := 99614876035902772561007607808 }, { target := 113, numerator := 99614876035902772561007607808 }, { target := 114, numerator := 96993431929694804862033723392 }, { target := 115, numerator := 96993431929694804862033723392 }, { target := 116, numerator := 3048739495519866433906627575808 }, { target := 117, numerator := 96993431929694804862033723392 }, { target := 118, numerator := 123207872991774481851772567552 }, { target := 119, numerator := 125829317097982449550746451968 }, { target := 216, numerator := 4606773975604423349535506432 }, { target := 217, numerator := 112940265208366507924096286720 }, { target := 218, numerator := 83516354009344707175450148864 }, { target := 219, numerator := 93175718796902369037379436544 }, { target := 220, numerator := 4606773975604423349535506432 }, { target := 221, numerator := 93027113184786097316426678272 }, { target := 222, numerator := 94661774918065086246907019264 }, { target := 223, numerator := 4606773975604423349535506432 }, { target := 224, numerator := 112940265208366507924096286720 }, { target := 225, numerator := 4606773975604423349535506432 }]

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
    Slot23.Left5.expected,
    Slot23.Left12.expected,
    Slot24.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 29410898455312150390898688 }, { target := 72, numerator := 426458027602026180668030976 }, { target := 73, numerator := 754879727019678526699732992 }, { target := 74, numerator := 24509082046093458659082240 }, { target := 75, numerator := 470574375284994406254379008 }, { target := 76, numerator := 24509082046093458659082240 }, { target := 77, numerator := 749977910610459834967916544 }, { target := 78, numerator := 784290625474990677090631680 }, { target := 79, numerator := 470574375284994406254379008 }, { target := 80, numerator := 12014352018995013434682114048 }, { target := 81, numerator := 769585176247334601895182336 }, { target := 82, numerator := 426458027602026180668030976 }, { target := 83, numerator := 749977910610459834967916544 }, { target := 84, numerator := 24509082046093458659082240 }, { target := 85, numerator := 769585176247334601895182336 }, { target := 86, numerator := 24509082046093458659082240 }, { target := 87, numerator := 749977910610459834967916544 }, { target := 88, numerator := 784290625474990677090631680 }, { target := 89, numerator := 29410898455312150390898688 }, { target := 226, numerator := 123207827799557344272584802304 }, { target := 227, numerator := 91750510063500149990222725120 }, { target := 228, numerator := 96993396352843015703949737984 }, { target := 229, numerator := 125829270944228777129448308736 }, { target := 230, numerator := 1685587942023731326963234635776 }, { target := 231, numerator := 3048738377252876412532257980416 }, { target := 232, numerator := 91750510063500149990222725120 }, { target := 233, numerator := 1685587942023731326963234635776 }, { target := 234, numerator := 99614839497514448560813244416 }, { target := 235, numerator := 99614839497514448560813244416 }, { target := 236, numerator := 96993396352843015703949737984 }, { target := 237, numerator := 96993396352843015703949737984 }, { target := 238, numerator := 3048738377252876412532257980416 }, { target := 239, numerator := 96993396352843015703949737984 }, { target := 240, numerator := 123207827799557344272584802304 }, { target := 241, numerator := 125829270944228777129448308736 }, { target := 624, numerator := 3158755209048234908039774208 }, { target := 625, numerator := 2352264517376345144284938240 }, { target := 626, numerator := 2486679632654993438244077568 }, { target := 627, numerator := 3225962766687559055019343872 }, { target := 628, numerator := 43214459562085426507863293952 }, { target := 629, numerator := 78162389534533982937239519232 }, { target := 630, numerator := 2352264517376345144284938240 }, { target := 631, numerator := 43214459562085426507863293952 }, { target := 632, numerator := 2553887190294317585223647232 }, { target := 633, numerator := 2553887190294317585223647232 }, { target := 634, numerator := 2486679632654993438244077568 }, { target := 635, numerator := 2486679632654993438244077568 }, { target := 636, numerator := 78162389534533982937239519232 }, { target := 637, numerator := 2486679632654993438244077568 }, { target := 638, numerator := 3158755209048234908039774208 }, { target := 639, numerator := 3225962766687559055019343872 }]

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
    Slot24.Left1.expected,
    Slot24.Left2.expected,
    Slot24.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 146, numerator := 441163476829682255863480320 }, { target := 147, numerator := 6396870414030392710020464640 }, { target := 148, numerator := 11323195905295177900495994880 }, { target := 149, numerator := 367636230691401879886233600 }, { target := 150, numerator := 7058615629274916093815685120 }, { target := 151, numerator := 367636230691401879886233600 }, { target := 152, numerator := 11249668659156897524518748160 }, { target := 153, numerator := 11764359382124860156359475200 }, { target := 154, numerator := 7058615629274916093815685120 }, { target := 155, numerator := 180215280284925201520231710720 }, { target := 156, numerator := 11543777643710019028427735040 }, { target := 157, numerator := 6396870414030392710020464640 }, { target := 158, numerator := 11249668659156897524518748160 }, { target := 159, numerator := 367636230691401879886233600 }, { target := 160, numerator := 11543777643710019028427735040 }, { target := 161, numerator := 367636230691401879886233600 }, { target := 162, numerator := 11249668659156897524518748160 }, { target := 163, numerator := 11764359382124860156359475200 }, { target := 164, numerator := 441163476829682255863480320 }, { target := 181, numerator := 774486992656553293626998784 }, { target := 182, numerator := 11230061393520022757591482368 }, { target := 183, numerator := 19878499478184867869759635456 }, { target := 184, numerator := 645405827213794411355832320 }, { target := 185, numerator := 12391791882504852698031980544 }, { target := 186, numerator := 645405827213794411355832320 }, { target := 187, numerator := 19749418312742108987488468992 }, { target := 188, numerator := 20652986470841421163386634240 }, { target := 189, numerator := 12391791882504852698031980544 }, { target := 190, numerator := 316377936500202020446629003264 }, { target := 191, numerator := 20265742974513144516573134848 }, { target := 192, numerator := 11230061393520022757591482368 }, { target := 193, numerator := 19749418312742108987488468992 }, { target := 194, numerator := 645405827213794411355832320 }, { target := 195, numerator := 20265742974513144516573134848 }, { target := 196, numerator := 645405827213794411355832320 }, { target := 197, numerator := 19749418312742108987488468992 }, { target := 198, numerator := 20652986470841421163386634240 }, { target := 199, numerator := 774486992656553293626998784 }, { target := 242, numerator := 29410898455312150390898688 }, { target := 243, numerator := 426458027602026180668030976 }, { target := 244, numerator := 754879727019678526699732992 }, { target := 245, numerator := 24509082046093458659082240 }, { target := 246, numerator := 470574375284994406254379008 }, { target := 247, numerator := 24509082046093458659082240 }, { target := 248, numerator := 749977910610459834967916544 }, { target := 249, numerator := 784290625474990677090631680 }, { target := 250, numerator := 470574375284994406254379008 }, { target := 251, numerator := 12014352018995013434682114048 }, { target := 252, numerator := 769585176247334601895182336 }, { target := 253, numerator := 426458027602026180668030976 }, { target := 254, numerator := 749977910610459834967916544 }, { target := 255, numerator := 24509082046093458659082240 }, { target := 256, numerator := 769585176247334601895182336 }, { target := 257, numerator := 24509082046093458659082240 }, { target := 258, numerator := 749977910610459834967916544 }, { target := 259, numerator := 784290625474990677090631680 }, { target := 260, numerator := 29410898455312150390898688 }]

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
    Slot24.Left4.expected,
    Slot24.Left5.expected,
    Slot24.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 277, numerator := 490181640921869173181644800 }, { target := 278, numerator := 7107633793367103011133849600 }, { target := 279, numerator := 12581328783661308778328883200 }, { target := 280, numerator := 408484700768224310984704000 }, { target := 281, numerator := 7842906254749906770906316800 }, { target := 282, numerator := 408484700768224310984704000 }, { target := 283, numerator := 12499631843507663916131942400 }, { target := 284, numerator := 13071510424583177951510528000 }, { target := 285, numerator := 7842906254749906770906316800 }, { target := 286, numerator := 200239200316583557244701900800 }, { target := 287, numerator := 12826419604122243364919705600 }, { target := 288, numerator := 7107633793367103011133849600 }, { target := 289, numerator := 12499631843507663916131942400 }, { target := 290, numerator := 408484700768224310984704000 }, { target := 291, numerator := 12826419604122243364919705600 }, { target := 292, numerator := 408484700768224310984704000 }, { target := 293, numerator := 12499631843507663916131942400 }, { target := 294, numerator := 13071510424583177951510528000 }, { target := 295, numerator := 490181640921869173181644800 }, { target := 312, numerator := 29410898455312150390898688 }, { target := 313, numerator := 426458027602026180668030976 }, { target := 314, numerator := 754879727019678526699732992 }, { target := 315, numerator := 24509082046093458659082240 }, { target := 316, numerator := 470574375284994406254379008 }, { target := 317, numerator := 24509082046093458659082240 }, { target := 318, numerator := 749977910610459834967916544 }, { target := 319, numerator := 784290625474990677090631680 }, { target := 320, numerator := 470574375284994406254379008 }, { target := 321, numerator := 12014352018995013434682114048 }, { target := 322, numerator := 769585176247334601895182336 }, { target := 323, numerator := 426458027602026180668030976 }, { target := 324, numerator := 749977910610459834967916544 }, { target := 325, numerator := 24509082046093458659082240 }, { target := 326, numerator := 769585176247334601895182336 }, { target := 327, numerator := 24509082046093458659082240 }, { target := 328, numerator := 749977910610459834967916544 }, { target := 329, numerator := 784290625474990677090631680 }, { target := 330, numerator := 29410898455312150390898688 }, { target := 413, numerator := 774486992656553293626998784 }, { target := 414, numerator := 11230061393520022757591482368 }, { target := 415, numerator := 19878499478184867869759635456 }, { target := 416, numerator := 645405827213794411355832320 }, { target := 417, numerator := 12391791882504852698031980544 }, { target := 418, numerator := 645405827213794411355832320 }, { target := 419, numerator := 19749418312742108987488468992 }, { target := 420, numerator := 20652986470841421163386634240 }, { target := 421, numerator := 12391791882504852698031980544 }, { target := 422, numerator := 316377936500202020446629003264 }, { target := 423, numerator := 20265742974513144516573134848 }, { target := 424, numerator := 11230061393520022757591482368 }, { target := 425, numerator := 19749418312742108987488468992 }, { target := 426, numerator := 645405827213794411355832320 }, { target := 427, numerator := 20265742974513144516573134848 }, { target := 428, numerator := 645405827213794411355832320 }, { target := 429, numerator := 19749418312742108987488468992 }, { target := 430, numerator := 20652986470841421163386634240 }, { target := 431, numerator := 774486992656553293626998784 }]

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
    Slot24.Left7.expected,
    Slot24.Left8.expected,
    Slot24.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 448, numerator := 769585176247334601895182336 }, { target := 449, numerator := 11158985055586351727480143872 }, { target := 450, numerator := 19752686190348254781976346624 }, { target := 451, numerator := 641320980206112168245985280 }, { target := 452, numerator := 12313362819957353630322917376 }, { target := 453, numerator := 641320980206112168245985280 }, { target := 454, numerator := 19624421994307032348327149568 }, { target := 455, numerator := 20522271366595589383871528960 }, { target := 456, numerator := 12313362819957353630322917376 }, { target := 457, numerator := 314375544497036184874181984256 }, { target := 458, numerator := 20137478778471922082923937792 }, { target := 459, numerator := 11158985055586351727480143872 }, { target := 460, numerator := 19624421994307032348327149568 }, { target := 461, numerator := 641320980206112168245985280 }, { target := 462, numerator := 20137478778471922082923937792 }, { target := 463, numerator := 641320980206112168245985280 }, { target := 464, numerator := 19624421994307032348327149568 }, { target := 465, numerator := 20522271366595589383871528960 }, { target := 466, numerator := 769585176247334601895182336 }, { target := 509, numerator := 490181640921869173181644800 }, { target := 510, numerator := 7107633793367103011133849600 }, { target := 511, numerator := 12581328783661308778328883200 }, { target := 512, numerator := 408484700768224310984704000 }, { target := 513, numerator := 7842906254749906770906316800 }, { target := 514, numerator := 408484700768224310984704000 }, { target := 515, numerator := 12499631843507663916131942400 }, { target := 516, numerator := 13071510424583177951510528000 }, { target := 517, numerator := 7842906254749906770906316800 }, { target := 518, numerator := 200239200316583557244701900800 }, { target := 519, numerator := 12826419604122243364919705600 }, { target := 520, numerator := 7107633793367103011133849600 }, { target := 521, numerator := 12499631843507663916131942400 }, { target := 522, numerator := 408484700768224310984704000 }, { target := 523, numerator := 12826419604122243364919705600 }, { target := 524, numerator := 408484700768224310984704000 }, { target := 525, numerator := 12499631843507663916131942400 }, { target := 526, numerator := 13071510424583177951510528000 }, { target := 527, numerator := 490181640921869173181644800 }, { target := 544, numerator := 11877101159536890066191253504 }, { target := 545, numerator := 172217966813284905959773175808 }, { target := 546, numerator := 304845596428113511698908839936 }, { target := 547, numerator := 9897584299614075055159377920 }, { target := 548, numerator := 190033618552590241059060056064 }, { target := 549, numerator := 9897584299614075055159377920 }, { target := 550, numerator := 302866079568190696687876964352 }, { target := 551, numerator := 316722697587650401765100093440 }, { target := 552, numerator := 190033618552590241059060056064 }, { target := 553, numerator := 4851795823670819592039127056384 }, { target := 554, numerator := 310784147007881956732004466688 }, { target := 555, numerator := 172217966813284905959773175808 }, { target := 556, numerator := 302866079568190696687876964352 }, { target := 557, numerator := 9897584299614075055159377920 }, { target := 558, numerator := 310784147007881956732004466688 }, { target := 559, numerator := 9897584299614075055159377920 }, { target := 560, numerator := 302866079568190696687876964352 }, { target := 561, numerator := 316722697587650401765100093440 }, { target := 562, numerator := 11877101159536890066191253504 }]

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

namespace RouteChunk19

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot24.Left10.expected,
    Slot24.Left11.expected,
    Slot24.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 579, numerator := 759781543428897218431549440 }, { target := 580, numerator := 11016832379719009667257466880 }, { target := 581, numerator := 19501059614675028606409768960 }, { target := 582, numerator := 633151286190747682026291200 }, { target := 583, numerator := 12156504694862355494904791040 }, { target := 584, numerator := 633151286190747682026291200 }, { target := 585, numerator := 19374429357436879070004510720 }, { target := 586, numerator := 20260841158103925824841318400 }, { target := 587, numerator := 12156504694862355494904791040 }, { target := 588, numerator := 310370760490704513729287946240 }, { target := 589, numerator := 19880950386389477215625543680 }, { target := 590, numerator := 11016832379719009667257466880 }, { target := 591, numerator := 19374429357436879070004510720 }, { target := 592, numerator := 633151286190747682026291200 }, { target := 593, numerator := 19880950386389477215625543680 }, { target := 594, numerator := 633151286190747682026291200 }, { target := 595, numerator := 19374429357436879070004510720 }, { target := 596, numerator := 20260841158103925824841318400 }, { target := 597, numerator := 759781543428897218431549440 }, { target := 640, numerator := 441163476829682255863480320 }, { target := 641, numerator := 6396870414030392710020464640 }, { target := 642, numerator := 11323195905295177900495994880 }, { target := 643, numerator := 367636230691401879886233600 }, { target := 644, numerator := 7058615629274916093815685120 }, { target := 645, numerator := 367636230691401879886233600 }, { target := 646, numerator := 11249668659156897524518748160 }, { target := 647, numerator := 11764359382124860156359475200 }, { target := 648, numerator := 7058615629274916093815685120 }, { target := 649, numerator := 180215280284925201520231710720 }, { target := 650, numerator := 11543777643710019028427735040 }, { target := 651, numerator := 6396870414030392710020464640 }, { target := 652, numerator := 11249668659156897524518748160 }, { target := 653, numerator := 367636230691401879886233600 }, { target := 654, numerator := 11543777643710019028427735040 }, { target := 655, numerator := 367636230691401879886233600 }, { target := 656, numerator := 11249668659156897524518748160 }, { target := 657, numerator := 11764359382124860156359475200 }, { target := 658, numerator := 441163476829682255863480320 }, { target := 675, numerator := 774486992656553293626998784 }, { target := 676, numerator := 11230061393520022757591482368 }, { target := 677, numerator := 19878499478184867869759635456 }, { target := 678, numerator := 645405827213794411355832320 }, { target := 679, numerator := 12391791882504852698031980544 }, { target := 680, numerator := 645405827213794411355832320 }, { target := 681, numerator := 19749418312742108987488468992 }, { target := 682, numerator := 20652986470841421163386634240 }, { target := 683, numerator := 12391791882504852698031980544 }, { target := 684, numerator := 316377936500202020446629003264 }, { target := 685, numerator := 20265742974513144516573134848 }, { target := 686, numerator := 11230061393520022757591482368 }, { target := 687, numerator := 19749418312742108987488468992 }, { target := 688, numerator := 645405827213794411355832320 }, { target := 689, numerator := 20265742974513144516573134848 }, { target := 690, numerator := 645405827213794411355832320 }, { target := 691, numerator := 19749418312742108987488468992 }, { target := 692, numerator := 20652986470841421163386634240 }, { target := 693, numerator := 774486992656553293626998784 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk19

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0
