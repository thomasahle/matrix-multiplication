import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk5Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 22; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent0

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
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 13614582570113187151085568 }, { target := 11, numerator := 329824242263064630660169728 }, { target := 12, numerator := 249893467174013015773151232 }, { target := 13, numerator := 278440172562960021089943552 }, { target := 14, numerator := 13614582570113187151085568 }, { target := 15, numerator := 278440172562960021089943552 }, { target := 16, numerator := 278000992480053144085069824 }, { target := 17, numerator := 13614582570113187151085568 }, { target := 18, numerator := 329824242263064630660169728 }, { target := 19, numerator := 13614582570113187151085568 }, { target := 24, numerator := 15371302901740695170580480 }, { target := 25, numerator := 372382209006685873325998080 }, { target := 26, numerator := 282137785519046953292267520 }, { target := 27, numerator := 314367936764632281875742720 }, { target := 28, numerator := 15371302901740695170580480 }, { target := 29, numerator := 314367936764632281875742720 }, { target := 30, numerator := 313872088283930969128304640 }, { target := 31, numerator := 15371302901740695170580480 }, { target := 32, numerator := 372382209006685873325998080 }, { target := 33, numerator := 15371302901740695170580480 }, { target := 55, numerator := 13175402487206310146211840 }, { target := 56, numerator := 319184750577159319993712640 }, { target := 57, numerator := 241832387587754531393372160 }, { target := 58, numerator := 269458231512541955893493760 }, { target := 59, numerator := 13175402487206310146211840 }, { target := 60, numerator := 269458231512541955893493760 }, { target := 61, numerator := 269033218529083687824261120 }, { target := 62, numerator := 13175402487206310146211840 }, { target := 63, numerator := 319184750577159319993712640 }, { target := 64, numerator := 13175402487206310146211840 }, { target := 69, numerator := 173476132748216416925122560 }, { target := 70, numerator := 4202599215932597713250549760 }, { target := 71, numerator := 3184126436572101330012733440 }, { target := 72, numerator := 3547866714915135752597667840 }, { target := 73, numerator := 173476132748216416925122560 }, { target := 74, numerator := 3547866714915135752597667840 }, { target := 75, numerator := 3542270710632935223019438080 }, { target := 76, numerator := 173476132748216416925122560 }, { target := 77, numerator := 4202599215932597713250549760 }, { target := 78, numerator := 173476132748216416925122560 }, { target := 95, numerator := 15371302901740695170580480 }, { target := 96, numerator := 372382209006685873325998080 }, { target := 97, numerator := 282137785519046953292267520 }, { target := 98, numerator := 314367936764632281875742720 }, { target := 99, numerator := 15371302901740695170580480 }, { target := 100, numerator := 314367936764632281875742720 }, { target := 101, numerator := 313872088283930969128304640 }, { target := 102, numerator := 15371302901740695170580480 }, { target := 103, numerator := 372382209006685873325998080 }, { target := 104, numerator := 15371302901740695170580480 }, { target := 144, numerator := 13175402487206310146211840 }, { target := 145, numerator := 319184750577159319993712640 }, { target := 146, numerator := 241832387587754531393372160 }, { target := 147, numerator := 269458231512541955893493760 }, { target := 148, numerator := 13175402487206310146211840 }, { target := 149, numerator := 269458231512541955893493760 }, { target := 150, numerator := 269033218529083687824261120 }, { target := 151, numerator := 13175402487206310146211840 }, { target := 152, numerator := 319184750577159319993712640 }, { target := 153, numerator := 13175402487206310146211840 }]

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
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 170, numerator := 15371302901740695170580480 }, { target := 171, numerator := 372382209006685873325998080 }, { target := 172, numerator := 282137785519046953292267520 }, { target := 173, numerator := 314367936764632281875742720 }, { target := 174, numerator := 15371302901740695170580480 }, { target := 175, numerator := 314367936764632281875742720 }, { target := 176, numerator := 313872088283930969128304640 }, { target := 177, numerator := 15371302901740695170580480 }, { target := 178, numerator := 372382209006685873325998080 }, { target := 179, numerator := 15371302901740695170580480 }, { target := 271, numerator := 15371302901740695170580480 }, { target := 272, numerator := 372382209006685873325998080 }, { target := 273, numerator := 282137785519046953292267520 }, { target := 274, numerator := 314367936764632281875742720 }, { target := 275, numerator := 15371302901740695170580480 }, { target := 276, numerator := 314367936764632281875742720 }, { target := 277, numerator := 313872088283930969128304640 }, { target := 278, numerator := 15371302901740695170580480 }, { target := 279, numerator := 372382209006685873325998080 }, { target := 280, numerator := 15371302901740695170580480 }, { target := 285, numerator := 637250300297878534071779328 }, { target := 286, numerator := 15437902436248605777029234688 }, { target := 287, numerator := 11696626479661060835059433472 }, { target := 288, numerator := 13032796464156612600048648192 }, { target := 289, numerator := 637250300297878534071779328 }, { target := 290, numerator := 13032796464156612600048648192 }, { target := 291, numerator := 13012240002856681034433429504 }, { target := 292, numerator := 637250300297878534071779328 }, { target := 293, numerator := 15437902436248605777029234688 }, { target := 294, numerator := 637250300297878534071779328 }, { target := 311, numerator := 15810482984647572175454208 }, { target := 312, numerator := 383021700692591183992455168 }, { target := 313, numerator := 290198865105305437672046592 }, { target := 314, numerator := 323349877815050347072192512 }, { target := 315, numerator := 15810482984647572175454208 }, { target := 316, numerator := 323349877815050347072192512 }, { target := 317, numerator := 322839862234900425389113344 }, { target := 318, numerator := 15810482984647572175454208 }, { target := 319, numerator := 383021700692591183992455168 }, { target := 320, numerator := 15810482984647572175454208 }, { target := 360, numerator := 173476132748216416925122560 }, { target := 361, numerator := 4202599215932597713250549760 }, { target := 362, numerator := 3184126436572101330012733440 }, { target := 363, numerator := 3547866714915135752597667840 }, { target := 364, numerator := 173476132748216416925122560 }, { target := 365, numerator := 3547866714915135752597667840 }, { target := 366, numerator := 3542270710632935223019438080 }, { target := 367, numerator := 173476132748216416925122560 }, { target := 368, numerator := 4202599215932597713250549760 }, { target := 369, numerator := 173476132748216416925122560 }, { target := 386, numerator := 637250300297878534071779328 }, { target := 387, numerator := 15437902436248605777029234688 }, { target := 388, numerator := 11696626479661060835059433472 }, { target := 389, numerator := 13032796464156612600048648192 }, { target := 390, numerator := 637250300297878534071779328 }, { target := 391, numerator := 13032796464156612600048648192 }, { target := 392, numerator := 13012240002856681034433429504 }, { target := 393, numerator := 637250300297878534071779328 }, { target := 394, numerator := 15437902436248605777029234688 }, { target := 395, numerator := 637250300297878534071779328 }]

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
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 41122115995940866228224000 }, { target := 35, numerator := 7212432801691834182008832000 }, { target := 40, numerator := 7212433666382962637144064000 }, { target := 48, numerator := 41121251304812411092992000 }, { target := 79, numerator := 596270681941142560309248000 }, { target := 80, numerator := 104580275624531595639128064000 }, { target := 85, numerator := 104580288162552958238588928000 }, { target := 93, numerator := 596258143919779960848384000 }, { target := 105, numerator := 1055467643895815566524416000 }, { target := 106, numerator := 185119108576757077338226688000 }, { target := 111, numerator := 185119130770496041020030976000 }, { target := 119, numerator := 1055445450156851884720128000 }, { target := 154, numerator := 34268429996617388523520000 }, { target := 155, numerator := 6010360668076528485007360000 }, { target := 160, numerator := 6010361388652468864286720000 }, { target := 168, numerator := 34267709420677009244160000 }, { target := 180, numerator := 657953855935053859651584000 }, { target := 181, numerator := 115398924827069346912141312000 }, { target := 186, numerator := 115398938662127402194305024000 }, { target := 194, numerator := 657940020876998577487872000 }, { target := 215, numerator := 34268429996617388523520000 }, { target := 216, numerator := 6010360668076528485007360000 }, { target := 221, numerator := 6010361388652468864286720000 }, { target := 229, numerator := 34267709420677009244160000 }, { target := 482, numerator := 13614582570113187151085568 }, { target := 483, numerator := 329824242263064630660169728 }, { target := 484, numerator := 249893467174013015773151232 }, { target := 485, numerator := 278440172562960021089943552 }, { target := 486, numerator := 13614582570113187151085568 }, { target := 487, numerator := 278440172562960021089943552 }, { target := 488, numerator := 278000992480053144085069824 }, { target := 489, numerator := 13614582570113187151085568 }, { target := 490, numerator := 329824242263064630660169728 }, { target := 491, numerator := 13614582570113187151085568 }, { target := 627, numerator := 15371302901740695170580480 }, { target := 628, numerator := 372382209006685873325998080 }, { target := 629, numerator := 282137785519046953292267520 }, { target := 630, numerator := 314367936764632281875742720 }, { target := 631, numerator := 15371302901740695170580480 }, { target := 632, numerator := 314367936764632281875742720 }, { target := 633, numerator := 313872088283930969128304640 }, { target := 634, numerator := 15371302901740695170580480 }, { target := 635, numerator := 372382209006685873325998080 }, { target := 636, numerator := 15371302901740695170580480 }, { target := 653, numerator := 15810482984647572175454208 }, { target := 654, numerator := 383021700692591183992455168 }, { target := 655, numerator := 290198865105305437672046592 }, { target := 656, numerator := 323349877815050347072192512 }, { target := 657, numerator := 15810482984647572175454208 }, { target := 658, numerator := 323349877815050347072192512 }, { target := 659, numerator := 322839862234900425389113344 }, { target := 660, numerator := 15810482984647572175454208 }, { target := 661, numerator := 383021700692591183992455168 }, { target := 662, numerator := 15810482984647572175454208 }, { target := 749, numerator := 15371302901740695170580480 }, { target := 750, numerator := 372382209006685873325998080 }, { target := 751, numerator := 282137785519046953292267520 }, { target := 752, numerator := 314367936764632281875742720 }, { target := 753, numerator := 15371302901740695170580480 }, { target := 754, numerator := 314367936764632281875742720 }, { target := 755, numerator := 313872088283930969128304640 }, { target := 756, numerator := 15371302901740695170580480 }, { target := 757, numerator := 372382209006685873325998080 }, { target := 758, numerator := 15371302901740695170580480 }]

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
    Slot1.Left16.expected,
    Slot1.Left17.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 86398415698851031343431680 }, { target := 122, numerator := 27830775099653679062408232960 }, { target := 124, numerator := 295991996814865791576428249088 }, { target := 132, numerator := 27830858981610668238166818816 }, { target := 139, numerator := 86398415698851031343431680 }, { target := 196, numerator := 64339245733186938234470400 }, { target := 197, numerator := 20725045286976143982644428800 }, { target := 199, numerator := 220419572096176653301595504640 }, { target := 207, numerator := 20725107752263263581613588480 }, { target := 214, numerator := 64339245733186938234470400 }, { target := 295, numerator := 1048613957896492088819712000 }, { target := 296, numerator := 183917036443141771641225216000 }, { target := 301, numerator := 183917058492765547247173632000 }, { target := 309, numerator := 1048591908272716482871296000 }, { target := 321, numerator := 1096589759891756432752640000 }, { target := 322, numerator := 192331541378448911520235520000 }, { target := 327, numerator := 192331564436879003657175040000 }, { target := 335, numerator := 1096566701461664295813120000 }, { target := 370, numerator := 657953855935053859651584000 }, { target := 371, numerator := 115398924827069346912141312000 }, { target := 376, numerator := 115398938662127402194305024000 }, { target := 384, numerator := 657940020876998577487872000 }, { target := 396, numerator := 16798384384341843854229504000 }, { target := 397, numerator := 2946278799491114263350607872000 }, { target := 402, numerator := 2946279152717440237273350144000 }, { target := 410, numerator := 16798031158015869931487232000 }, { target := 431, numerator := 1076028701893785999638528000 }, { target := 432, numerator := 188725324977602994429231104000 }, { target := 437, numerator := 188725347603687522338603008000 }, { target := 445, numerator := 1076006075809258090266624000 }, { target := 492, numerator := 596270681941142560309248000 }, { target := 493, numerator := 104580275624531595639128064000 }, { target := 498, numerator := 104580288162552958238588928000 }, { target := 506, numerator := 596258143919779960848384000 }, { target := 527, numerator := 1048613957896492088819712000 }, { target := 528, numerator := 183917036443141771641225216000 }, { target := 533, numerator := 183917058492765547247173632000 }, { target := 541, numerator := 1048591908272716482871296000 }, { target := 637, numerator := 34268429996617388523520000 }, { target := 638, numerator := 6010360668076528485007360000 }, { target := 643, numerator := 6010361388652468864286720000 }, { target := 651, numerator := 34267709420677009244160000 }, { target := 663, numerator := 1076028701893785999638528000 }, { target := 664, numerator := 188725324977602994429231104000 }, { target := 669, numerator := 188725347603687522338603008000 }, { target := 677, numerator := 1076006075809258090266624000 }, { target := 698, numerator := 34268429996617388523520000 }, { target := 699, numerator := 6010360668076528485007360000 }, { target := 704, numerator := 6010361388652468864286720000 }, { target := 712, numerator := 34267709420677009244160000 }, { target := 759, numerator := 1048613957896492088819712000 }, { target := 760, numerator := 183917036443141771641225216000 }, { target := 765, numerator := 183917058492765547247173632000 }, { target := 773, numerator := 1048591908272716482871296000 }, { target := 794, numerator := 1096589759891756432752640000 }, { target := 795, numerator := 192331541378448911520235520000 }, { target := 800, numerator := 192331564436879003657175040000 }, { target := 808, numerator := 1096566701461664295813120000 }, { target := 890, numerator := 41122115995940866228224000 }, { target := 891, numerator := 7212432801691834182008832000 }, { target := 896, numerator := 7212433666382962637144064000 }, { target := 904, numerator := 41121251304812411092992000 }]

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
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 231, numerator := 68015774060797620419297280 }, { target := 232, numerator := 21909333589089066495938396160 }, { target := 234, numerator := 233014976215958176347400962048 }, { target := 242, numerator := 21909399623821164357705793536 }, { target := 249, numerator := 68015774060797620419297280 }, { target := 337, numerator := 88236679862656372435845120 }, { target := 338, numerator := 28422919250710140319055216640 }, { target := 340, numerator := 302289698874756553099330977792 }, { target := 348, numerator := 28423004917389618626212921344 }, { target := 355, numerator := 88236679862656372435845120 }, { target := 412, numerator := 1182003857326834322421841920 }, { target := 413, numerator := 380748689129304588024010506240 }, { target := 415, numerator := 4049422424509759659226454556672 }, { target := 423, numerator := 380749836705865099513643925504 }, { target := 430, numerator := 1182003857326834322421841920 }, { target := 447, numerator := 2137901222505611690476830720 }, { target := 448, numerator := 688663647678664441480442019840 }, { target := 450, numerator := 7324227495652955651135873482752 }, { target := 458, numerator := 688665723310919301297617240064 }, { target := 465, numerator := 2137901222505611690476830720 }, { target := 508, numerator := 64339245733186938234470400 }, { target := 509, numerator := 20725045286976143982644428800 }, { target := 511, numerator := 220419572096176653301595504640 }, { target := 519, numerator := 20725107752263263581613588480 }, { target := 526, numerator := 64339245733186938234470400 }, { target := 543, numerator := 1182003857326834322421841920 }, { target := 544, numerator := 380748689129304588024010506240 }, { target := 546, numerator := 4049422424509759659226454556672 }, { target := 554, numerator := 380749836705865099513643925504 }, { target := 561, numerator := 1182003857326834322421841920 }, { target := 578, numerator := 69854038224602961511710720 }, { target := 579, numerator := 22501477740145527752585379840 }, { target := 581, numerator := 239312678275848937870303690752 }, { target := 589, numerator := 22501545559600114745751896064 }, { target := 596, numerator := 69854038224602961511710720 }, { target := 679, numerator := 69854038224602961511710720 }, { target := 680, numerator := 22501477740145527752585379840 }, { target := 682, numerator := 239312678275848937870303690752 }, { target := 690, numerator := 22501545559600114745751896064 }, { target := 697, numerator := 69854038224602961511710720 }, { target := 714, numerator := 68015774060797620419297280 }, { target := 715, numerator := 21909333589089066495938396160 }, { target := 717, numerator := 233014976215958176347400962048 }, { target := 725, numerator := 21909399623821164357705793536 }, { target := 732, numerator := 68015774060797620419297280 }, { target := 775, numerator := 68015774060797620419297280 }, { target := 776, numerator := 21909333589089066495938396160 }, { target := 778, numerator := 233014976215958176347400962048 }, { target := 786, numerator := 21909399623821164357705793536 }, { target := 793, numerator := 68015774060797620419297280 }, { target := 810, numerator := 2137901222505611690476830720 }, { target := 811, numerator := 688663647678664441480442019840 }, { target := 813, numerator := 7324227495652955651135873482752 }, { target := 821, numerator := 688665723310919301297617240064 }, { target := 828, numerator := 2137901222505611690476830720 }, { target := 845, numerator := 68015774060797620419297280 }, { target := 846, numerator := 21909333589089066495938396160 }, { target := 848, numerator := 233014976215958176347400962048 }, { target := 856, numerator := 21909399623821164357705793536 }, { target := 863, numerator := 68015774060797620419297280 }]

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
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 522894497343003296457031680 }, { target := 252, numerator := 20464050225647964185868369920 }, { target := 255, numerator := 20464057731166959176442183680 }, { target := 262, numerator := 522902002861998287030845440 }, { target := 466, numerator := 12819348967118790493785292800 }, { target := 468, numerator := 501699295854595251008385843200 }, { target := 471, numerator := 501699479860867386261163212800 }, { target := 478, numerator := 12819532973390925746562662400 }, { target := 562, numerator := 9479571209895737180930703360 }, { target := 564, numerator := 370993426671424382982516899840 }, { target := 567, numerator := 370993562739220356682597007360 }, { target := 574, numerator := 9479707277691710881010810880 }, { target := 597, numerator := 10575962897873002157372866560 }, { target := 599, numerator := 413901919080041082081918320640 }, { target := 602, numerator := 413902070885215593665459650560 }, { target := 609, numerator := 10576114703047513740914196480 }, { target := 613, numerator := 24923674708243847179258560512 }, { target := 616, numerator := 89336290973254787590210453504 }, { target := 618, numerator := 24930917485651309889501265920 }, { target := 733, numerator := 522894497343003296457031680 }, { target := 735, numerator := 20464050225647964185868369920 }, { target := 738, numerator := 20464057731166959176442183680 }, { target := 745, numerator := 522902002861998287030845440 }, { target := 829, numerator := 10559095333442582696196833280 }, { target := 831, numerator := 413241788427600825172696760320 }, { target := 834, numerator := 413241939990661820788800225280 }, { target := 841, numerator := 10559246896503578312300298240 }, { target := 864, numerator := 10744638542177196769133199360 }, { target := 866, numerator := 420503225604443651174133923840 }, { target := 869, numerator := 420503379830753322432053903360 }, { target := 876, numerator := 10744792768486868027053178880 }, { target := 880, numerator := 24850940248978544123287961600 }, { target := 883, numerator := 89075581952904822256775987200 }, { target := 885, numerator := 24858161889876062876205056000 }, { target := 906, numerator := 86398415698851031343431680 }, { target := 907, numerator := 27830775099653679062408232960 }, { target := 909, numerator := 295991996814865791576428249088 }, { target := 917, numerator := 27830858981610668238166818816 }, { target := 924, numerator := 86398415698851031343431680 }, { target := 925, numerator := 522894497343003296457031680 }, { target := 927, numerator := 20464050225647964185868369920 }, { target := 930, numerator := 20464057731166959176442183680 }, { target := 937, numerator := 522902002861998287030845440 }, { target := 941, numerator := 88236679862656372435845120 }, { target := 942, numerator := 28422919250710140319055216640 }, { target := 944, numerator := 302289698874756553099330977792 }, { target := 952, numerator := 28423004917389618626212921344 }, { target := 959, numerator := 88236679862656372435845120 }, { target := 960, numerator := 12819348967118790493785292800 }, { target := 962, numerator := 501699295854595251008385843200 }, { target := 965, numerator := 501699479860867386261163212800 }, { target := 972, numerator := 12819532973390925746562662400 }, { target := 976, numerator := 24681226510692836992689897472 }, { target := 979, numerator := 88467260905421569812095565824 }, { target := 981, numerator := 24688398833067153178513899520 }, { target := 986, numerator := 522894497343003296457031680 }, { target := 988, numerator := 20464050225647964185868369920 }, { target := 991, numerator := 20464057731166959176442183680 }, { target := 998, numerator := 522902002861998287030845440 }, { target := 1002, numerator := 24850940248978544123287961600 }, { target := 1005, numerator := 89075581952904822256775987200 }, { target := 1007, numerator := 24858161889876062876205056000 }, { target := 1012, numerator := 39614067090032720187836334080 }, { target := 1014, numerator := 39614095424231617405707616256 }]

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
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 3510168063282387374856732672 }, { target := 2, numerator := 3510168063282387374856732672 }, { target := 3, numerator := 3510168063282387374856732672 }, { target := 4, numerator := 3510168063282387374856732672 }, { target := 10, numerator := 696280450221135679289556992 }, { target := 12, numerator := 31470609648236828087331848192 }, { target := 17, numerator := 699996709478610559597281280 }, { target := 34, numerator := 50644060507782744685674496 }, { target := 35, numerator := 10044481551451212439407820800 }, { target := 40, numerator := 10044481551451212439407820800 }, { target := 48, numerator := 50644060507782744685674496 }, { target := 51, numerator := 12786702140818068213849915392 }, { target := 52, numerator := 12786702140818068213849915392 }, { target := 53, numerator := 12786702140818068213849915392 }, { target := 54, numerator := 12786702140818068213849915392 }, { target := 55, numerator := 27837163212726630816768065536 }, { target := 57, numerator := 1258189134713961159342356955136 }, { target := 62, numerator := 27985738568329792172840714240 }, { target := 79, numerator := 8299586141114345545290219520 }, { target := 80, numerator := 1646097075219552145816682496000 }, { target := 85, numerator := 1646097075219552145816682496000 }, { target := 93, numerator := 8299586141114345545290219520 }, { target := 121, numerator := 49855826102992351772278784 }, { target := 122, numerator := 8170409703120347949254574080 }, { target := 124, numerator := 84117531383046578839098490880 }, { target := 132, numerator := 8170409703120347949254574080 }, { target := 139, numerator := 49855826102992351772278784 }, { target := 140, numerator := 3510170424465628809679339520 }, { target := 141, numerator := 3510170424465628809679339520 }, { target := 142, numerator := 3510170424465628809679339520 }, { target := 143, numerator := 3510170424465628809679339520 }, { target := 144, numerator := 27837156409824346791426916352 }, { target := 146, numerator := 1258188827235154038352932503552 }, { target := 151, numerator := 27985731729118362051731783680 }, { target := 154, numerator := 85447452827837829097424158720 }, { target := 155, numerator := 16947206739392845959351238656000 }, { target := 160, numerator := 16947206739392845959351238656000 }, { target := 168, numerator := 85447452827837829097424158720 }, { target := 196, numerator := 9888147208237963996771123200 }, { target := 197, numerator := 1620476887278391801134710784000 }, { target := 199, numerator := 16683436984694124621462503424000 }, { target := 207, numerator := 1620476887278391801134710784000 }, { target := 214, numerator := 9888147208237963996771123200 }, { target := 482, numerator := 696280450221135679289556992 }, { target := 484, numerator := 31470609648236828087331848192 }, { target := 489, numerator := 699996709478610559597281280 }, { target := 492, numerator := 8299586141114345545290219520 }, { target := 493, numerator := 1646097075219552145816682496000 }, { target := 498, numerator := 1646097075219552145816682496000 }, { target := 506, numerator := 8299586141114345545290219520 }, { target := 508, numerator := 9888147208237963996771123200 }, { target := 509, numerator := 1620476887278391801134710784000 }, { target := 511, numerator := 16683436984694124621462503424000 }, { target := 519, numerator := 1620476887278391801134710784000 }, { target := 526, numerator := 9888147208237963996771123200 }, { target := 890, numerator := 50644060507782744685674496 }, { target := 891, numerator := 10044481551451212439407820800 }, { target := 896, numerator := 10044481551451212439407820800 }, { target := 904, numerator := 50644060507782744685674496 }, { target := 906, numerator := 49855826102992351772278784 }, { target := 907, numerator := 8170409703120347949254574080 }, { target := 909, numerator := 84117531383046578839098490880 }, { target := 917, numerator := 8170409703120347949254574080 }, { target := 924, numerator := 49855826102992351772278784 }]

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
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left7.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 39614067090032720187836334080 }, { target := 1, numerator := 24923674708243847179258560512 }, { target := 2, numerator := 24850940248978544123287961600 }, { target := 3, numerator := 24681226510692836992689897472 }, { target := 4, numerator := 24850940248978544123287961600 }, { target := 10, numerator := 537834340124231962070089728 }, { target := 11, numerator := 13185616080465041650750586880 }, { target := 12, numerator := 9750416101607043957528723456 }, { target := 13, numerator := 10878133266383659361869234176 }, { target := 14, numerator := 537834340124231962070089728 }, { target := 15, numerator := 10860783771540942201802457088 }, { target := 16, numerator := 11051628214810830962537005056 }, { target := 17, numerator := 537834340124231962070089728 }, { target := 18, numerator := 13185616080465041650750586880 }, { target := 19, numerator := 537834340124231962070089728 }, { target := 50, numerator := 39614095424231617405707616256 }, { target := 51, numerator := 89336290973254787590210453504 }, { target := 52, numerator := 89075581952904822256775987200 }, { target := 53, numerator := 88467260905421569812095565824 }, { target := 54, numerator := 89075581952904822256775987200 }, { target := 55, numerator := 21048737374952191734036037632 }, { target := 56, numerator := 516033561450440829608625438720 }, { target := 57, numerator := 381593238862036508210588811264 }, { target := 58, numerator := 425727688196613684427115986944 }, { target := 59, numerator := 21048737374952191734036037632 }, { target := 60, numerator := 425048696668389420177630953472 }, { target := 61, numerator := 432517603478856326921966321664 }, { target := 62, numerator := 21048737374952191734036037632 }, { target := 63, numerator := 516033561450440829608625438720 }, { target := 64, numerator := 21048737374952191734036037632 }, { target := 140, numerator := 24930917485651309889501265920 }, { target := 141, numerator := 24858161889876062876205056000 }, { target := 142, numerator := 24688398833067153178513899520 }, { target := 143, numerator := 24858161889876062876205056000 }, { target := 250, numerator := 716759286992345552209838080 }, { target := 252, numerator := 28655903307218590546673008640 }, { target := 255, numerator := 28655896304230945226468884480 }, { target := 262, numerator := 716759286992345552209838080 }, { target := 562, numerator := 32396215814361440678135726080 }, { target := 564, numerator := 1295194697499665899323014512640 }, { target := 567, numerator := 1295194380977364451245665812480 }, { target := 574, numerator := 32396215814361440678135726080 }, { target := 613, numerator := 3510168063282387374856732672 }, { target := 616, numerator := 12786702140818068213849915392 }, { target := 618, numerator := 3510170424465628809679339520 }, { target := 880, numerator := 3510168063282387374856732672 }, { target := 883, numerator := 12786702140818068213849915392 }, { target := 885, numerator := 3510170424465628809679339520 }, { target := 925, numerator := 720584847992687340761907200 }, { target := 927, numerator := 28808848526221844883806617600 }, { target := 930, numerator := 28808841485857137406194483200 }, { target := 937, numerator := 720584847992687340761907200 }, { target := 976, numerator := 3510168063282387374856732672 }, { target := 979, numerator := 12786702140818068213849915392 }, { target := 981, numerator := 3510170424465628809679339520 }, { target := 1002, numerator := 3510168063282387374856732672 }, { target := 1005, numerator := 12786702140818068213849915392 }, { target := 1007, numerator := 3510170424465628809679339520 }]

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
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 83942646777178263010672640 }, { target := 35, numerator := 62510481642579557561139200 }, { target := 36, numerator := 66082509165012675136061440 }, { target := 37, numerator := 85728660538394821798133760 }, { target := 38, numerator := 1148406848462247300337500160 }, { target := 39, numerator := 2077134004294857869817282560 }, { target := 40, numerator := 62510481642579557561139200 }, { target := 41, numerator := 1148406848462247300337500160 }, { target := 42, numerator := 67868522926229233923522560 }, { target := 43, numerator := 67868522926229233923522560 }, { target := 44, numerator := 66082509165012675136061440 }, { target := 45, numerator := 66082509165012675136061440 }, { target := 46, numerator := 2077134004294857869817282560 }, { target := 47, numerator := 66082509165012675136061440 }, { target := 48, numerator := 83942646777178263010672640 }, { target := 49, numerator := 85728660538394821798133760 }, { target := 79, numerator := 27039719476666106789316526080 }, { target := 80, numerator := 20135961312410930587788902400 }, { target := 81, numerator := 21286587673120126621376839680 }, { target := 82, numerator := 27615032657020704806110494720 }, { target := 83, numerator := 369926374968006524798521835520 }, { target := 84, numerator := 669089228752397493531385528320 }, { target := 85, numerator := 20135961312410930587788902400 }, { target := 86, numerator := 369926374968006524798521835520 }, { target := 87, numerator := 21861900853474724638170808320 }, { target := 88, numerator := 21861900853474724638170808320 }, { target := 89, numerator := 21286587673120126621376839680 }, { target := 90, numerator := 21286587673120126621376839680 }, { target := 91, numerator := 669089228752397493531385528320 }, { target := 92, numerator := 21286587673120126621376839680 }, { target := 93, numerator := 27039719476666106789316526080 }, { target := 94, numerator := 27615032657020704806110494720 }, { target := 144, numerator := 21048745094914586581483388928 }, { target := 145, numerator := 516033750714035025868625018880 }, { target := 146, numerator := 381593378817483795444956921856 }, { target := 147, numerator := 425727844339078896341615640576 }, { target := 148, numerator := 21048745094914586581483388928 }, { target := 149, numerator := 425048852561823587097051660288 }, { target := 150, numerator := 432517762111631988787255443456 }, { target := 151, numerator := 21048745094914586581483388928 }, { target := 152, numerator := 516033750714035025868625018880 }, { target := 153, numerator := 21048745094914586581483388928 }, { target := 482, numerator := 537842060086626809517441024 }, { target := 483, numerator := 13185805344059237910750167040 }, { target := 484, numerator := 9750556057054331191896834048 }, { target := 485, numerator := 10878289408848871276368887808 }, { target := 486, numerator := 537842060086626809517441024 }, { target := 487, numerator := 10860939664975109121223163904 }, { target := 488, numerator := 11051786847586492827826126848 }, { target := 489, numerator := 537842060086626809517441024 }, { target := 490, numerator := 13185805344059237910750167040 }, { target := 491, numerator := 537842060086626809517441024 }]

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
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 154, numerator := 287578787603073740653067239424 }, { target := 155, numerator := 214154416300161296231007518720 }, { target := 156, numerator := 226391811517313370301350805504 }, { target := 157, numerator := 293697485211649777688238882816 }, { target := 158, numerator := 3934322562314391813615366701056 }, { target := 159, numerator := 7116045318773931071904621264896 }, { target := 160, numerator := 214154416300161296231007518720 }, { target := 161, numerator := 3934322562314391813615366701056 }, { target := 162, numerator := 232510509125889407336522448896 }, { target := 163, numerator := 232510509125889407336522448896 }, { target := 164, numerator := 226391811517313370301350805504 }, { target := 165, numerator := 226391811517313370301350805504 }, { target := 166, numerator := 7116045318773931071904621264896 }, { target := 167, numerator := 226391811517313370301350805504 }, { target := 168, numerator := 287578787603073740653067239424 }, { target := 169, numerator := 293697485211649777688238882816 }, { target := 492, numerator := 27039800974381424438115565568 }, { target := 493, numerator := 20136022002198933092213719040 }, { target := 494, numerator := 21286651830896014983197360128 }, { target := 495, numerator := 27615115888729965383607386112 }, { target := 496, numerator := 369927489926111827951240609792 }, { target := 497, numerator := 669091245387353119606987292672 }, { target := 498, numerator := 20136022002198933092213719040 }, { target := 499, numerator := 369927489926111827951240609792 }, { target := 500, numerator := 21861966745244555928689180672 }, { target := 501, numerator := 21861966745244555928689180672 }, { target := 502, numerator := 21286651830896014983197360128 }, { target := 503, numerator := 21286651830896014983197360128 }, { target := 504, numerator := 669091245387353119606987292672 }, { target := 505, numerator := 21286651830896014983197360128 }, { target := 506, numerator := 27039800974381424438115565568 }, { target := 507, numerator := 27615115888729965383607386112 }, { target := 890, numerator := 83942646777178263010672640 }, { target := 891, numerator := 62510481642579557561139200 }, { target := 892, numerator := 66082509165012675136061440 }, { target := 893, numerator := 85728660538394821798133760 }, { target := 894, numerator := 1148406848462247300337500160 }, { target := 895, numerator := 2077134004294857869817282560 }, { target := 896, numerator := 62510481642579557561139200 }, { target := 897, numerator := 1148406848462247300337500160 }, { target := 898, numerator := 67868522926229233923522560 }, { target := 899, numerator := 67868522926229233923522560 }, { target := 900, numerator := 66082509165012675136061440 }, { target := 901, numerator := 66082509165012675136061440 }, { target := 902, numerator := 2077134004294857869817282560 }, { target := 903, numerator := 66082509165012675136061440 }, { target := 904, numerator := 83942646777178263010672640 }, { target := 905, numerator := 85728660538394821798133760 }]

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
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 41780069851875920087875584 }, { target := 122, numerator := 605811012852200841274195968 }, { target := 123, numerator := 1072355126198148615588806656 }, { target := 124, numerator := 34816724876563266739896320 }, { target := 125, numerator := 668481117630014721406009344 }, { target := 126, numerator := 34816724876563266739896320 }, { target := 127, numerator := 1065391781222835962240827392 }, { target := 128, numerator := 1114135196050024535676682240 }, { target := 129, numerator := 668481117630014721406009344 }, { target := 130, numerator := 17067158534491313355897176064 }, { target := 131, numerator := 1093245161124086575632744448 }, { target := 132, numerator := 605811012852200841274195968 }, { target := 133, numerator := 1065391781222835962240827392 }, { target := 134, numerator := 34816724876563266739896320 }, { target := 135, numerator := 1093245161124086575632744448 }, { target := 136, numerator := 34816724876563266739896320 }, { target := 137, numerator := 1065391781222835962240827392 }, { target := 138, numerator := 1114135196050024535676682240 }, { target := 139, numerator := 41780069851875920087875584 }, { target := 196, numerator := 7327831726518903528920973312 }, { target := 197, numerator := 106253560034524101169354113024 }, { target := 198, numerator := 188081014313985190575638315008 }, { target := 199, numerator := 6106526438765752940767477760 }, { target := 200, numerator := 117245307624302456462735572992 }, { target := 201, numerator := 6106526438765752940767477760 }, { target := 202, numerator := 186859709026232039987484819456 }, { target := 203, numerator := 195408846040504094104559288320 }, { target := 204, numerator := 117245307624302456462735572992 }, { target := 205, numerator := 2993419260282972091564217597952 }, { target := 206, numerator := 191744930177244642340098801664 }, { target := 207, numerator := 106253560034524101169354113024 }, { target := 208, numerator := 186859709026232039987484819456 }, { target := 209, numerator := 6106526438765752940767477760 }, { target := 210, numerator := 191744930177244642340098801664 }, { target := 211, numerator := 6106526438765752940767477760 }, { target := 212, numerator := 186859709026232039987484819456 }, { target := 213, numerator := 195408846040504094104559288320 }, { target := 214, numerator := 7327831726518903528920973312 }, { target := 508, numerator := 7327832605045090039338369024 }, { target := 509, numerator := 106253572773153805570406350848 }, { target := 510, numerator := 188081036862823977676351471616 }, { target := 511, numerator := 6106527170870908366115307520 }, { target := 512, numerator := 117245321680721440629413904384 }, { target := 513, numerator := 6106527170870908366115307520 }, { target := 514, numerator := 186859731428649796003128410112 }, { target := 515, numerator := 195408869467869067715689840640 }, { target := 516, numerator := 117245321680721440629413904384 }, { target := 517, numerator := 2993419619160919281069723746304 }, { target := 518, numerator := 191744953165346522696020656128 }, { target := 519, numerator := 106253572773153805570406350848 }, { target := 520, numerator := 186859731428649796003128410112 }, { target := 521, numerator := 6106527170870908366115307520 }, { target := 522, numerator := 191744953165346522696020656128 }, { target := 523, numerator := 6106527170870908366115307520 }, { target := 524, numerator := 186859731428649796003128410112 }, { target := 525, numerator := 195408869467869067715689840640 }, { target := 526, numerator := 7327832605045090039338369024 }]

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
    Slot16.Left14.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 13614582570113187151085568 }, { target := 251, numerator := 15371302901740695170580480 }, { target := 252, numerator := 13175402487206310146211840 }, { target := 253, numerator := 173476132748216416925122560 }, { target := 254, numerator := 15371302901740695170580480 }, { target := 255, numerator := 13175402487206310146211840 }, { target := 256, numerator := 15371302901740695170580480 }, { target := 257, numerator := 15371302901740695170580480 }, { target := 258, numerator := 637250300297878534071779328 }, { target := 259, numerator := 15810482984647572175454208 }, { target := 260, numerator := 173476132748216416925122560 }, { target := 261, numerator := 637250300297878534071779328 }, { target := 262, numerator := 13614582570113187151085568 }, { target := 263, numerator := 15371302901740695170580480 }, { target := 264, numerator := 15810482984647572175454208 }, { target := 265, numerator := 15371302901740695170580480 }, { target := 466, numerator := 329824242263064630660169728 }, { target := 467, numerator := 372382209006685873325998080 }, { target := 468, numerator := 319184750577159319993712640 }, { target := 469, numerator := 4202599215932597713250549760 }, { target := 470, numerator := 372382209006685873325998080 }, { target := 471, numerator := 319184750577159319993712640 }, { target := 472, numerator := 372382209006685873325998080 }, { target := 473, numerator := 372382209006685873325998080 }, { target := 474, numerator := 15437902436248605777029234688 }, { target := 475, numerator := 383021700692591183992455168 }, { target := 476, numerator := 4202599215932597713250549760 }, { target := 477, numerator := 15437902436248605777029234688 }, { target := 478, numerator := 329824242263064630660169728 }, { target := 479, numerator := 372382209006685873325998080 }, { target := 480, numerator := 383021700692591183992455168 }, { target := 481, numerator := 372382209006685873325998080 }, { target := 906, numerator := 41779191325689409670479872 }, { target := 907, numerator := 605798274222496440221958144 }, { target := 908, numerator := 1072332577359361514875650048 }, { target := 909, numerator := 34815992771407841392066560 }, { target := 910, numerator := 668467061211030554727677952 }, { target := 911, numerator := 34815992771407841392066560 }, { target := 912, numerator := 1065369378805079946597236736 }, { target := 913, numerator := 1114111768685050924546129920 }, { target := 914, numerator := 668467061211030554727677952 }, { target := 915, numerator := 17066799656544123850391027712 }, { target := 916, numerator := 1093222173022206219710889984 }, { target := 917, numerator := 605798274222496440221958144 }, { target := 918, numerator := 1065369378805079946597236736 }, { target := 919, numerator := 34815992771407841392066560 }, { target := 920, numerator := 1093222173022206219710889984 }, { target := 921, numerator := 34815992771407841392066560 }, { target := 922, numerator := 1065369378805079946597236736 }, { target := 923, numerator := 1114111768685050924546129920 }, { target := 924, numerator := 41779191325689409670479872 }]

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
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot17.Left4.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 562, numerator := 249893467174013015773151232 }, { target := 563, numerator := 282137785519046953292267520 }, { target := 564, numerator := 241832387587754531393372160 }, { target := 565, numerator := 3184126436572101330012733440 }, { target := 566, numerator := 282137785519046953292267520 }, { target := 567, numerator := 241832387587754531393372160 }, { target := 568, numerator := 282137785519046953292267520 }, { target := 569, numerator := 282137785519046953292267520 }, { target := 570, numerator := 11696626479661060835059433472 }, { target := 571, numerator := 290198865105305437672046592 }, { target := 572, numerator := 3184126436572101330012733440 }, { target := 573, numerator := 11696626479661060835059433472 }, { target := 574, numerator := 249893467174013015773151232 }, { target := 575, numerator := 282137785519046953292267520 }, { target := 576, numerator := 290198865105305437672046592 }, { target := 577, numerator := 282137785519046953292267520 }, { target := 597, numerator := 278440172562960021089943552 }, { target := 598, numerator := 314367936764632281875742720 }, { target := 599, numerator := 269458231512541955893493760 }, { target := 600, numerator := 3547866714915135752597667840 }, { target := 601, numerator := 314367936764632281875742720 }, { target := 602, numerator := 269458231512541955893493760 }, { target := 603, numerator := 314367936764632281875742720 }, { target := 604, numerator := 314367936764632281875742720 }, { target := 605, numerator := 13032796464156612600048648192 }, { target := 606, numerator := 323349877815050347072192512 }, { target := 607, numerator := 3547866714915135752597667840 }, { target := 608, numerator := 13032796464156612600048648192 }, { target := 609, numerator := 278440172562960021089943552 }, { target := 610, numerator := 314367936764632281875742720 }, { target := 611, numerator := 323349877815050347072192512 }, { target := 612, numerator := 314367936764632281875742720 }, { target := 733, numerator := 13614582570113187151085568 }, { target := 734, numerator := 15371302901740695170580480 }, { target := 735, numerator := 13175402487206310146211840 }, { target := 736, numerator := 173476132748216416925122560 }, { target := 737, numerator := 15371302901740695170580480 }, { target := 738, numerator := 13175402487206310146211840 }, { target := 739, numerator := 15371302901740695170580480 }, { target := 740, numerator := 15371302901740695170580480 }, { target := 741, numerator := 637250300297878534071779328 }, { target := 742, numerator := 15810482984647572175454208 }, { target := 743, numerator := 173476132748216416925122560 }, { target := 744, numerator := 637250300297878534071779328 }, { target := 745, numerator := 13614582570113187151085568 }, { target := 746, numerator := 15371302901740695170580480 }, { target := 747, numerator := 15810482984647572175454208 }, { target := 748, numerator := 15371302901740695170580480 }, { target := 829, numerator := 278440172562960021089943552 }, { target := 830, numerator := 314367936764632281875742720 }, { target := 831, numerator := 269458231512541955893493760 }, { target := 832, numerator := 3547866714915135752597667840 }, { target := 833, numerator := 314367936764632281875742720 }, { target := 834, numerator := 269458231512541955893493760 }, { target := 835, numerator := 314367936764632281875742720 }, { target := 836, numerator := 314367936764632281875742720 }, { target := 837, numerator := 13032796464156612600048648192 }, { target := 838, numerator := 323349877815050347072192512 }, { target := 839, numerator := 3547866714915135752597667840 }, { target := 840, numerator := 13032796464156612600048648192 }, { target := 841, numerator := 278440172562960021089943552 }, { target := 842, numerator := 314367936764632281875742720 }, { target := 843, numerator := 323349877815050347072192512 }, { target := 844, numerator := 314367936764632281875742720 }]

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
    Slot17.Left6.expected,
    Slot17.Left7.expected,
    Slot17.Left8.expected,
    Slot17.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 864, numerator := 278000992480053144085069824 }, { target := 865, numerator := 313872088283930969128304640 }, { target := 866, numerator := 269033218529083687824261120 }, { target := 867, numerator := 3542270710632935223019438080 }, { target := 868, numerator := 313872088283930969128304640 }, { target := 869, numerator := 269033218529083687824261120 }, { target := 870, numerator := 313872088283930969128304640 }, { target := 871, numerator := 313872088283930969128304640 }, { target := 872, numerator := 13012240002856681034433429504 }, { target := 873, numerator := 322839862234900425389113344 }, { target := 874, numerator := 3542270710632935223019438080 }, { target := 875, numerator := 13012240002856681034433429504 }, { target := 876, numerator := 278000992480053144085069824 }, { target := 877, numerator := 313872088283930969128304640 }, { target := 878, numerator := 322839862234900425389113344 }, { target := 879, numerator := 313872088283930969128304640 }, { target := 925, numerator := 13614582570113187151085568 }, { target := 926, numerator := 15371302901740695170580480 }, { target := 927, numerator := 13175402487206310146211840 }, { target := 928, numerator := 173476132748216416925122560 }, { target := 929, numerator := 15371302901740695170580480 }, { target := 930, numerator := 13175402487206310146211840 }, { target := 931, numerator := 15371302901740695170580480 }, { target := 932, numerator := 15371302901740695170580480 }, { target := 933, numerator := 637250300297878534071779328 }, { target := 934, numerator := 15810482984647572175454208 }, { target := 935, numerator := 173476132748216416925122560 }, { target := 936, numerator := 637250300297878534071779328 }, { target := 937, numerator := 13614582570113187151085568 }, { target := 938, numerator := 15371302901740695170580480 }, { target := 939, numerator := 15810482984647572175454208 }, { target := 940, numerator := 15371302901740695170580480 }, { target := 960, numerator := 329824242263064630660169728 }, { target := 961, numerator := 372382209006685873325998080 }, { target := 962, numerator := 319184750577159319993712640 }, { target := 963, numerator := 4202599215932597713250549760 }, { target := 964, numerator := 372382209006685873325998080 }, { target := 965, numerator := 319184750577159319993712640 }, { target := 966, numerator := 372382209006685873325998080 }, { target := 967, numerator := 372382209006685873325998080 }, { target := 968, numerator := 15437902436248605777029234688 }, { target := 969, numerator := 383021700692591183992455168 }, { target := 970, numerator := 4202599215932597713250549760 }, { target := 971, numerator := 15437902436248605777029234688 }, { target := 972, numerator := 329824242263064630660169728 }, { target := 973, numerator := 372382209006685873325998080 }, { target := 974, numerator := 383021700692591183992455168 }, { target := 975, numerator := 372382209006685873325998080 }, { target := 986, numerator := 13614582570113187151085568 }, { target := 987, numerator := 15371302901740695170580480 }, { target := 988, numerator := 13175402487206310146211840 }, { target := 989, numerator := 173476132748216416925122560 }, { target := 990, numerator := 15371302901740695170580480 }, { target := 991, numerator := 13175402487206310146211840 }, { target := 992, numerator := 15371302901740695170580480 }, { target := 993, numerator := 15371302901740695170580480 }, { target := 994, numerator := 637250300297878534071779328 }, { target := 995, numerator := 15810482984647572175454208 }, { target := 996, numerator := 173476132748216416925122560 }, { target := 997, numerator := 637250300297878534071779328 }, { target := 998, numerator := 13614582570113187151085568 }, { target := 999, numerator := 15371302901740695170580480 }, { target := 1000, numerator := 15810482984647572175454208 }, { target := 1001, numerator := 15371302901740695170580480 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent0
