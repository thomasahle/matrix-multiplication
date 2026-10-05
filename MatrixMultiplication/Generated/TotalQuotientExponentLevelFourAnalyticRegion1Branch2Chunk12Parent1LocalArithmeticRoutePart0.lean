import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 51; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent1

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
    Slot2.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 11333679558887148512870400 }, { target := 251, numerator := 13458744476178488859033600 }, { target := 252, numerator := 10271147100241478339788800 }, { target := 253, numerator := 105899068378351793917132800 }, { target := 254, numerator := 12750389503748042076979200 }, { target := 255, numerator := 10271147100241478339788800 }, { target := 256, numerator := 12750389503748042076979200 }, { target := 257, numerator := 12750389503748042076979200 }, { target := 258, numerator := 546141683743874468963942400 }, { target := 259, numerator := 12750389503748042076979200 }, { target := 260, numerator := 105899068378351793917132800 }, { target := 261, numerator := 546141683743874468963942400 }, { target := 262, numerator := 11333679558887148512870400 }, { target := 263, numerator := 12750389503748042076979200 }, { target := 264, numerator := 12750389503748042076979200 }, { target := 265, numerator := 13458744476178488859033600 }, { target := 466, numerator := 227126938360098456197922816 }, { target := 467, numerator := 269713239302616916735033344 }, { target := 468, numerator := 205833787888839225929367552 }, { target := 469, numerator := 2122217330302169950099341312 }, { target := 470, numerator := 255517805655110763222663168 }, { target := 471, numerator := 205833787888839225929367552 }, { target := 472, numerator := 255517805655110763222663168 }, { target := 473, numerator := 255517805655110763222663168 }, { target := 474, numerator := 10944679342227244358037405696 }, { target := 475, numerator := 255517805655110763222663168 }, { target := 476, numerator := 2122217330302169950099341312 }, { target := 477, numerator := 10944679342227244358037405696 }, { target := 478, numerator := 227126938360098456197922816 }, { target := 479, numerator := 255517805655110763222663168 }, { target := 480, numerator := 255517805655110763222663168 }, { target := 481, numerator := 269713239302616916735033344 }, { target := 562, numerator := 381264980360963675972960256 }, { target := 563, numerator := 452752164178644365217890304 }, { target := 564, numerator := 345521388452123331350495232 }, { target := 565, numerator := 3562444660247754347372347392 }, { target := 566, numerator := 428923102906084135469580288 }, { target := 567, numerator := 345521388452123331350495232 }, { target := 568, numerator := 428923102906084135469580288 }, { target := 569, numerator := 428923102906084135469580288 }, { target := 570, numerator := 18372206241143937135947022336 }, { target := 571, numerator := 428923102906084135469580288 }, { target := 572, numerator := 3562444660247754347372347392 }, { target := 573, numerator := 18372206241143937135947022336 }, { target := 574, numerator := 381264980360963675972960256 }, { target := 575, numerator := 428923102906084135469580288 }, { target := 576, numerator := 428923102906084135469580288 }, { target := 577, numerator := 452752164178644365217890304 }, { target := 613, numerator := 3710812420045939657366568960 }, { target := 616, numerator := 13275186425336582085562859520 }, { target := 618, numerator := 3710811186419929728040304640 }, { target := 880, numerator := 3391751912901802789630377984 }, { target := 883, numerator := 12133768527083343252037828608 }, { target := 885, numerator := 3391750785344571284134035456 }, { target := 976, numerator := 3710812420045939657366568960 }, { target := 979, numerator := 13275186425336582085562859520 }, { target := 981, numerator := 3710811186419929728040304640 }, { target := 1002, numerator := 3391751912901802789630377984 }, { target := 1005, numerator := 12133768527083343252037828608 }, { target := 1007, numerator := 3391750785344571284134035456 }, { target := 1012, numerator := 39614081257132168796771975168 }, { target := 1014, numerator := 39614081257132168796771975168 }]

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
    Slot2.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 597, numerator := 365851176160877153995456512 }, { target := 598, numerator := 434448271691041620369604608 }, { target := 599, numerator := 331552628395794920808382464 }, { target := 600, numerator := 3418421927253195907645046784 }, { target := 601, numerator := 411582573180986798244888576 }, { target := 602, numerator := 331552628395794920808382464 }, { target := 603, numerator := 411582573180986798244888576 }, { target := 604, numerator := 411582573180986798244888576 }, { target := 605, numerator := 17629453551252267858156060672 }, { target := 606, numerator := 411582573180986798244888576 }, { target := 607, numerator := 3418421927253195907645046784 }, { target := 608, numerator := 17629453551252267858156060672 }, { target := 609, numerator := 365851176160877153995456512 }, { target := 610, numerator := 411582573180986798244888576 }, { target := 611, numerator := 411582573180986798244888576 }, { target := 612, numerator := 434448271691041620369604608 }, { target := 733, numerator := 11333679558887148512870400 }, { target := 734, numerator := 13458744476178488859033600 }, { target := 735, numerator := 10271147100241478339788800 }, { target := 736, numerator := 105899068378351793917132800 }, { target := 737, numerator := 12750389503748042076979200 }, { target := 738, numerator := 10271147100241478339788800 }, { target := 739, numerator := 12750389503748042076979200 }, { target := 740, numerator := 12750389503748042076979200 }, { target := 741, numerator := 546141683743874468963942400 }, { target := 742, numerator := 12750389503748042076979200 }, { target := 743, numerator := 105899068378351793917132800 }, { target := 744, numerator := 546141683743874468963942400 }, { target := 745, numerator := 11333679558887148512870400 }, { target := 746, numerator := 12750389503748042076979200 }, { target := 747, numerator := 12750389503748042076979200 }, { target := 748, numerator := 13458744476178488859033600 }, { target := 829, numerator := 365851176160877153995456512 }, { target := 830, numerator := 434448271691041620369604608 }, { target := 831, numerator := 331552628395794920808382464 }, { target := 832, numerator := 3418421927253195907645046784 }, { target := 833, numerator := 411582573180986798244888576 }, { target := 834, numerator := 331552628395794920808382464 }, { target := 835, numerator := 411582573180986798244888576 }, { target := 836, numerator := 411582573180986798244888576 }, { target := 837, numerator := 17629453551252267858156060672 }, { target := 838, numerator := 411582573180986798244888576 }, { target := 839, numerator := 3418421927253195907645046784 }, { target := 840, numerator := 17629453551252267858156060672 }, { target := 841, numerator := 365851176160877153995456512 }, { target := 842, numerator := 411582573180986798244888576 }, { target := 843, numerator := 411582573180986798244888576 }, { target := 844, numerator := 434448271691041620369604608 }, { target := 864, numerator := 244354131289606921937485824 }, { target := 865, numerator := 290170530906408219800764416 }, { target := 866, numerator := 221445931481206273005846528 }, { target := 867, numerator := 2283183914237264676853383168 }, { target := 868, numerator := 274898397700807787179671552 }, { target := 869, numerator := 221445931481206273005846528 }, { target := 870, numerator := 274898397700807787179671552 }, { target := 871, numerator := 274898397700807787179671552 }, { target := 872, numerator := 11774814701517933550862598144 }, { target := 873, numerator := 274898397700807787179671552 }, { target := 874, numerator := 2283183914237264676853383168 }, { target := 875, numerator := 11774814701517933550862598144 }, { target := 876, numerator := 244354131289606921937485824 }, { target := 877, numerator := 274898397700807787179671552 }, { target := 878, numerator := 274898397700807787179671552 }, { target := 879, numerator := 290170530906408219800764416 }]

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
  [{ target := 250, numerator := 3574977984932403213112442880 }, { target := 252, numerator := 132019180863670636343879270400 }, { target := 255, numerator := 132019148535503949188384686080 }, { target := 262, numerator := 3575010313099090368607027200 }, { target := 613, numerator := 28108970350183886423353982976 }, { target := 616, numerator := 102238384328160902340379934720 }, { target := 618, numerator := 28108970350183886423353982976 }, { target := 880, numerator := 28108970350183886423353982976 }, { target := 883, numerator := 102238384328160902340379934720 }, { target := 885, numerator := 28108970350183886423353982976 }, { target := 925, numerator := 11787026741242634453385216 }, { target := 926, numerator := 13997094255225628413394944 }, { target := 927, numerator := 10681992984251137473380352 }, { target := 928, numerator := 110135031113485865673818112 }, { target := 929, numerator := 13260405083897963760058368 }, { target := 930, numerator := 10681992984251137473380352 }, { target := 931, numerator := 13260405083897963760058368 }, { target := 932, numerator := 13260405083897963760058368 }, { target := 933, numerator := 567987351093629447722500096 }, { target := 934, numerator := 13260405083897963760058368 }, { target := 935, numerator := 110135031113485865673818112 }, { target := 936, numerator := 567987351093629447722500096 }, { target := 937, numerator := 11787026741242634453385216 }, { target := 938, numerator := 13260405083897963760058368 }, { target := 939, numerator := 13260405083897963760058368 }, { target := 940, numerator := 13997094255225628413394944 }, { target := 960, numerator := 227126938360098456197922816 }, { target := 961, numerator := 269713239302616916735033344 }, { target := 962, numerator := 205833787888839225929367552 }, { target := 963, numerator := 2122217330302169950099341312 }, { target := 964, numerator := 255517805655110763222663168 }, { target := 965, numerator := 205833787888839225929367552 }, { target := 966, numerator := 255517805655110763222663168 }, { target := 967, numerator := 255517805655110763222663168 }, { target := 968, numerator := 10944679342227244358037405696 }, { target := 969, numerator := 255517805655110763222663168 }, { target := 970, numerator := 2122217330302169950099341312 }, { target := 971, numerator := 10944679342227244358037405696 }, { target := 972, numerator := 227126938360098456197922816 }, { target := 973, numerator := 255517805655110763222663168 }, { target := 974, numerator := 255517805655110763222663168 }, { target := 975, numerator := 269713239302616916735033344 }, { target := 976, numerator := 28108970350183886423353982976 }, { target := 979, numerator := 102238384328160902340379934720 }, { target := 981, numerator := 28108970350183886423353982976 }, { target := 986, numerator := 10880332376531662572355584 }, { target := 987, numerator := 12920394697131349304672256 }, { target := 988, numerator := 9860301216231819206197248 }, { target := 989, numerator := 101663105643217722160447488 }, { target := 990, numerator := 12240373923598120393900032 }, { target := 991, numerator := 9860301216231819206197248 }, { target := 992, numerator := 12240373923598120393900032 }, { target := 993, numerator := 12240373923598120393900032 }, { target := 994, numerator := 524296016394119490205384704 }, { target := 995, numerator := 12240373923598120393900032 }, { target := 996, numerator := 101663105643217722160447488 }, { target := 997, numerator := 524296016394119490205384704 }, { target := 998, numerator := 10880332376531662572355584 }, { target := 999, numerator := 12240373923598120393900032 }, { target := 1000, numerator := 12240373923598120393900032 }, { target := 1001, numerator := 12920394697131349304672256 }, { target := 1002, numerator := 28108970350183886423353982976 }, { target := 1005, numerator := 102238384328160902340379934720 }, { target := 1007, numerator := 28108970350183886423353982976 }]

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
    Slot4.Left2.expected,
    Slot4.Left7.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 80472220462338623825510400 }, { target := 122, numerator := 1351933303767288880268574720 }, { target := 123, numerator := 2929188824829125907248578560 }, { target := 124, numerator := 96566664554806348590612480 }, { target := 125, numerator := 1545066632876901577449799680 }, { target := 126, numerator := 112661108647274073355714560 }, { target := 127, numerator := 2929188824829125907248578560 }, { target := 128, numerator := 2929188824829125907248578560 }, { target := 129, numerator := 1545066632876901577449799680 }, { target := 130, numerator := 36148121431682509822419271680 }, { target := 131, numerator := 2896999936644190457718374400 }, { target := 132, numerator := 1351933303767288880268574720 }, { target := 133, numerator := 2929188824829125907248578560 }, { target := 134, numerator := 112661108647274073355714560 }, { target := 135, numerator := 2896999936644190457718374400 }, { target := 136, numerator := 112661108647274073355714560 }, { target := 137, numerator := 2929188824829125907248578560 }, { target := 138, numerator := 2929188824829125907248578560 }, { target := 139, numerator := 96566664554806348590612480 }, { target := 196, numerator := 6737869402164169921517322240 }, { target := 197, numerator := 113196205956358054681491013632 }, { target := 198, numerator := 245258446238775785143230529536 }, { target := 199, numerator := 8085443282597003905820786688 }, { target := 200, numerator := 129367092521552062493132587008 }, { target := 201, numerator := 9433017163029837890124251136 }, { target := 202, numerator := 245258446238775785143230529536 }, { target := 203, numerator := 245258446238775785143230529536 }, { target := 204, numerator := 129367092521552062493132587008 }, { target := 205, numerator := 3026650935452145128745581150208 }, { target := 206, numerator := 242563298477910117174623600640 }, { target := 207, numerator := 113196205956358054681491013632 }, { target := 208, numerator := 245258446238775785143230529536 }, { target := 209, numerator := 9433017163029837890124251136 }, { target := 210, numerator := 242563298477910117174623600640 }, { target := 211, numerator := 9433017163029837890124251136 }, { target := 212, numerator := 245258446238775785143230529536 }, { target := 213, numerator := 245258446238775785143230529536 }, { target := 214, numerator := 8085443282597003905820786688 }, { target := 562, numerator := 34627498041467741278683791360 }, { target := 564, numerator := 1278747434546612931478211788800 }, { target := 567, numerator := 1278747121413627676217583861760 }, { target := 574, numerator := 34627811174452996539311718400 }, { target := 925, numerator := 3574977984932403213112442880 }, { target := 927, numerator := 132019180863670636343879270400 }, { target := 930, numerator := 132019148535503949188384686080 }, { target := 937, numerator := 3575010313099090368607027200 }]

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
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 582953660340917868114739200 }, { target := 252, numerator := 21903066584491184781420134400 }, { target := 255, numerator := 21901410009227290433342668800 }, { target := 262, numerator := 584610235604812216192204800 }, { target := 466, numerator := 13953277934611647036810854400 }, { target := 468, numerator := 524260496957821261542378700800 }, { target := 471, numerator := 524220846027311274243234201600 }, { target := 478, numerator := 13992928865121634335955353600 }, { target := 508, numerator := 6737871840593152164998676480 }, { target := 509, numerator := 113196246921964956371977764864 }, { target := 510, numerator := 245258534997590738805951823872 }, { target := 511, numerator := 8085446208711782597998411776 }, { target := 512, numerator := 129367139339388521567974588416 }, { target := 513, numerator := 9433020576830413030998147072 }, { target := 514, numerator := 245258534997590738805951823872 }, { target := 515, numerator := 245258534997590738805951823872 }, { target := 516, numerator := 129367139339388521567974588416 }, { target := 517, numerator := 3026652030794443952517405474816 }, { target := 518, numerator := 242563386261353477939952353280 }, { target := 519, numerator := 113196246921964956371977764864 }, { target := 520, numerator := 245258534997590738805951823872 }, { target := 521, numerator := 9433020576830413030998147072 }, { target := 522, numerator := 242563386261353477939952353280 }, { target := 523, numerator := 9433020576830413030998147072 }, { target := 524, numerator := 245258534997590738805951823872 }, { target := 525, numerator := 245258534997590738805951823872 }, { target := 526, numerator := 8085446208711782597998411776 }, { target := 562, numerator := 10436751015780948929150976000 }, { target := 564, numerator := 392135546915890566248005632000 }, { target := 567, numerator := 392105888874875683564683264000 }, { target := 574, numerator := 10466409056795831612473344000 }, { target := 597, numerator := 12110392169662938937609420800 }, { target := 599, numerator := 455018544529429774168856985600 }, { target := 602, numerator := 454984130514270162550731571200 }, { target := 609, numerator := 12144806184822550555734835200 }, { target := 733, numerator := 582953660340917868114739200 }, { target := 735, numerator := 21903066584491184781420134400 }, { target := 738, numerator := 21901410009227290433342668800 }, { target := 745, numerator := 584610235604812216192204800 }, { target := 829, numerator := 12091587212877748038637977600 }, { target := 831, numerator := 454311993994446187563004723200 }, { target := 834, numerator := 454277633417198314472236646400 }, { target := 841, numerator := 12125947790125621129406054400 }, { target := 906, numerator := 80469782033356380344156160 }, { target := 907, numerator := 1351892338160387189781823488 }, { target := 908, numerator := 2929100066014172244527284224 }, { target := 909, numerator := 96563738440027656412987392 }, { target := 910, numerator := 1545019815040442502607798272 }, { target := 911, numerator := 112657694846698932481818624 }, { target := 912, numerator := 2929100066014172244527284224 }, { target := 913, numerator := 2929100066014172244527284224 }, { target := 914, numerator := 1545019815040442502607798272 }, { target := 915, numerator := 36147026089383686050594947072 }, { target := 916, numerator := 2896912153200829692389621760 }, { target := 917, numerator := 1351892338160387189781823488 }, { target := 918, numerator := 2929100066014172244527284224 }, { target := 919, numerator := 112657694846698932481818624 }, { target := 920, numerator := 2896912153200829692389621760 }, { target := 921, numerator := 112657694846698932481818624 }, { target := 922, numerator := 2929100066014172244527284224 }, { target := 923, numerator := 2929100066014172244527284224 }, { target := 924, numerator := 96563738440027656412987392 }]

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
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 173915914656148698704117760 }, { target := 35, numerator := 135267933621448987880980480 }, { target := 36, numerator := 154591924138798843292549120 }, { target := 37, numerator := 181645510863088640868745216 }, { target := 38, numerator := 2144962947425833950684119040 }, { target := 39, numerator := 4823268033130523910727532544 }, { target := 40, numerator := 135267933621448987880980480 }, { target := 41, numerator := 2144962947425833950684119040 }, { target := 42, numerator := 154591924138798843292549120 }, { target := 43, numerator := 150727126035328872210235392 }, { target := 44, numerator := 150727126035328872210235392 }, { target := 45, numerator := 150727126035328872210235392 }, { target := 46, numerator := 4823268033130523910727532544 }, { target := 47, numerator := 150727126035328872210235392 }, { target := 48, numerator := 173915914656148698704117760 }, { target := 49, numerator := 181645510863088640868745216 }, { target := 121, numerator := 132298922308507685414240256 }, { target := 122, numerator := 21121151591750788570511572992 }, { target := 124, numerator := 210757330879226727474734825472 }, { target := 132, numerator := 21121151591750788570511572992 }, { target := 139, numerator := 132283826584830311191805952 }, { target := 196, numerator := 11124916078488015532155994112 }, { target := 197, numerator := 1776061624986803965744522461184 }, { target := 199, numerator := 17722424174325653883447509254144 }, { target := 207, numerator := 1776061624986803965744522461184 }, { target := 214, numerator := 11123646690528352362880303104 }, { target := 508, numerator := 11124913394558810401454161920 }, { target := 509, numerator := 1776061196505039988084640317440 }, { target := 511, numerator := 17722419898722000642080023511040 }, { target := 519, numerator := 1776061196505039988084640317440 }, { target := 526, numerator := 11123644006905392006839664640 }, { target := 864, numerator := 12148002083233320735552307200 }, { target := 866, numerator := 456431645599396947380561510400 }, { target := 869, numerator := 456397124708413858707721420800 }, { target := 876, numerator := 12182522974216409408392396800 }, { target := 906, numerator := 132301606237712816116072448 }, { target := 907, numerator := 21121580073514766230393716736 }, { target := 909, numerator := 210761606482879968842220568576 }, { target := 917, numerator := 21121580073514766230393716736 }, { target := 924, numerator := 132286510207790667232444416 }, { target := 925, numerator := 582953660340917868114739200 }, { target := 927, numerator := 21903066584491184781420134400 }, { target := 930, numerator := 21901410009227290433342668800 }, { target := 937, numerator := 584610235604812216192204800 }, { target := 960, numerator := 13953277934611647036810854400 }, { target := 962, numerator := 524260496957821261542378700800 }, { target := 965, numerator := 524220846027311274243234201600 }, { target := 972, numerator := 13992928865121634335955353600 }, { target := 986, numerator := 582953660340917868114739200 }, { target := 988, numerator := 21903066584491184781420134400 }, { target := 991, numerator := 21901410009227290433342668800 }, { target := 998, numerator := 584610235604812216192204800 }]

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
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 79, numerator := 25686470458877760575278940160 }, { target := 80, numerator := 19978365912460480447439175680 }, { target := 81, numerator := 22832418185669120511359057920 }, { target := 82, numerator := 26828091368161216600846893056 }, { target := 83, numerator := 316799802326159047095106928640 }, { target := 84, numerator := 712371447392876559954402607104 }, { target := 85, numerator := 19978365912460480447439175680 }, { target := 86, numerator := 316799802326159047095106928640 }, { target := 87, numerator := 22832418185669120511359057920 }, { target := 88, numerator := 22261607731027392498575081472 }, { target := 89, numerator := 22261607731027392498575081472 }, { target := 90, numerator := 22261607731027392498575081472 }, { target := 91, numerator := 712371447392876559954402607104 }, { target := 92, numerator := 22261607731027392498575081472 }, { target := 93, numerator := 25686470458877760575278940160 }, { target := 94, numerator := 26828091368161216600846893056 }, { target := 154, numerator := 267725785827901794576393830400 }, { target := 155, numerator := 208231166755034729114972979200 }, { target := 156, numerator := 237978476291468261845683404800 }, { target := 157, numerator := 279624709642475207668678000640 }, { target := 158, numerator := 3301951358544122133108857241600 }, { target := 159, numerator := 7424928460293809769585322229760 }, { target := 160, numerator := 208231166755034729114972979200 }, { target := 161, numerator := 3301951358544122133108857241600 }, { target := 162, numerator := 237978476291468261845683404800 }, { target := 163, numerator := 232029014384181555299541319680 }, { target := 164, numerator := 232029014384181555299541319680 }, { target := 165, numerator := 232029014384181555299541319680 }, { target := 166, numerator := 7424928460293809769585322229760 }, { target := 167, numerator := 232029014384181555299541319680 }, { target := 168, numerator := 267725785827901794576393830400 }, { target := 169, numerator := 279624709642475207668678000640 }, { target := 492, numerator := 25686470458877760575278940160 }, { target := 493, numerator := 19978365912460480447439175680 }, { target := 494, numerator := 22832418185669120511359057920 }, { target := 495, numerator := 26828091368161216600846893056 }, { target := 496, numerator := 316799802326159047095106928640 }, { target := 497, numerator := 712371447392876559954402607104 }, { target := 498, numerator := 19978365912460480447439175680 }, { target := 499, numerator := 316799802326159047095106928640 }, { target := 500, numerator := 22832418185669120511359057920 }, { target := 501, numerator := 22261607731027392498575081472 }, { target := 502, numerator := 22261607731027392498575081472 }, { target := 503, numerator := 22261607731027392498575081472 }, { target := 504, numerator := 712371447392876559954402607104 }, { target := 505, numerator := 22261607731027392498575081472 }, { target := 506, numerator := 25686470458877760575278940160 }, { target := 507, numerator := 26828091368161216600846893056 }, { target := 890, numerator := 173915914656148698704117760 }, { target := 891, numerator := 135267933621448987880980480 }, { target := 892, numerator := 154591924138798843292549120 }, { target := 893, numerator := 181645510863088640868745216 }, { target := 894, numerator := 2144962947425833950684119040 }, { target := 895, numerator := 4823268033130523910727532544 }, { target := 896, numerator := 135267933621448987880980480 }, { target := 897, numerator := 2144962947425833950684119040 }, { target := 898, numerator := 154591924138798843292549120 }, { target := 899, numerator := 150727126035328872210235392 }, { target := 900, numerator := 150727126035328872210235392 }, { target := 901, numerator := 150727126035328872210235392 }, { target := 902, numerator := 4823268033130523910727532544 }, { target := 903, numerator := 150727126035328872210235392 }, { target := 904, numerator := 173915914656148698704117760 }, { target := 905, numerator := 181645510863088640868745216 }]

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
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected,
    Slot9.Left10.expected,
    Slot9.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 172968144004071594079027200 }, { target := 122, numerator := 25546489693434285040808755200 }, { target := 124, numerator := 266266789719847833843007488000 }, { target := 132, numerator := 25546489693434285040808755200 }, { target := 139, numerator := 172968144004071594079027200 }, { target := 196, numerator := 134530778669833462061465600 }, { target := 197, numerator := 19869491983782221698406809600 }, { target := 199, numerator := 207096392004326092989005824000 }, { target := 207, numerator := 19869491983782221698406809600 }, { target := 214, numerator := 134530778669833462061465600 }, { target := 231, numerator := 153749461336952528070246400 }, { target := 232, numerator := 22707990838608253369607782400 }, { target := 234, numerator := 236681590862086963416006656000 }, { target := 242, numerator := 22707990838608253369607782400 }, { target := 249, numerator := 153749461336952528070246400 }, { target := 337, numerator := 180655617070919220482539520 }, { target := 338, numerator := 26681889235364697709289144320 }, { target := 340, numerator := 278100869262952182013807820800 }, { target := 348, numerator := 26681889235364697709289144320 }, { target := 355, numerator := 180655617070919220482539520 }, { target := 412, numerator := 2133273776050216326974668800 }, { target := 413, numerator := 315073372885689515503307980800 }, { target := 415, numerator := 3283957073211456617397092352000 }, { target := 423, numerator := 315073372885689515503307980800 }, { target := 430, numerator := 2133273776050216326974668800 }, { target := 447, numerator := 4796983193712918875791687680 }, { target := 448, numerator := 708489314164577505131762810880 }, { target := 450, numerator := 7384465634897113258579407667200 }, { target := 458, numerator := 708489314164577505131762810880 }, { target := 465, numerator := 4796983193712918875791687680 }, { target := 508, numerator := 134530778669833462061465600 }, { target := 509, numerator := 19869491983782221698406809600 }, { target := 511, numerator := 207096392004326092989005824000 }, { target := 519, numerator := 19869491983782221698406809600 }, { target := 526, numerator := 134530778669833462061465600 }, { target := 543, numerator := 2133273776050216326974668800 }, { target := 544, numerator := 315073372885689515503307980800 }, { target := 546, numerator := 3283957073211456617397092352000 }, { target := 554, numerator := 315073372885689515503307980800 }, { target := 561, numerator := 2133273776050216326974668800 }, { target := 578, numerator := 153749461336952528070246400 }, { target := 579, numerator := 22707990838608253369607782400 }, { target := 581, numerator := 236681590862086963416006656000 }, { target := 589, numerator := 22707990838608253369607782400 }, { target := 596, numerator := 153749461336952528070246400 }, { target := 679, numerator := 149905724803528714868490240 }, { target := 680, numerator := 22140291067643047035367587840 }, { target := 682, numerator := 230764551090534789330606489600 }, { target := 690, numerator := 22140291067643047035367587840 }, { target := 697, numerator := 149905724803528714868490240 }, { target := 714, numerator := 149905724803528714868490240 }, { target := 715, numerator := 22140291067643047035367587840 }, { target := 717, numerator := 230764551090534789330606489600 }, { target := 725, numerator := 22140291067643047035367587840 }, { target := 732, numerator := 149905724803528714868490240 }, { target := 775, numerator := 149905724803528714868490240 }, { target := 776, numerator := 22140291067643047035367587840 }, { target := 778, numerator := 230764551090534789330606489600 }, { target := 786, numerator := 22140291067643047035367587840 }, { target := 793, numerator := 149905724803528714868490240 }]

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
    Slot9.Left12.expected,
    Slot9.Left13.expected,
    Slot9.Left14.expected,
    Slot9.Left15.expected,
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
  [{ target := 10, numerator := 575180944869705629873209344 }, { target := 11, numerator := 13767234228816825076320043008 }, { target := 12, numerator := 10297594335570536276762296320 }, { target := 13, numerator := 11948920274067433085107961856 }, { target := 14, numerator := 575180944869705629873209344 }, { target := 15, numerator := 11930366050039378064789471232 }, { target := 16, numerator := 11986028722123543125744943104 }, { target := 17, numerator := 575180944869705629873209344 }, { target := 18, numerator := 13767234228816825076320043008 }, { target := 19, numerator := 575180944869705629873209344 }, { target := 34, numerator := 130839743018340321236877312 }, { target := 35, numerator := 11002214798210574184374861824 }, { target := 40, numerator := 11002212143883529404379299840 }, { target := 48, numerator := 130842397345385101232439296 }, { target := 55, numerator := 21611025696697968984334532608 }, { target := 56, numerator := 517270356998383644721813651456 }, { target := 57, numerator := 386907072957012025364698890240 }, { target := 58, numerator := 448951630602370710513272225792 }, { target := 59, numerator := 21611025696697968984334532608 }, { target := 60, numerator := 448254500741186905062164660224 }, { target := 61, numerator := 450345890324738321415487356928 }, { target := 62, numerator := 21611025696697968984334532608 }, { target := 63, numerator := 517270356998383644721813651456 }, { target := 64, numerator := 21611025696697968984334532608 }, { target := 79, numerator := 20888197713900596049513283584 }, { target := 80, numerator := 1756472710005331863181163757568 }, { target := 85, numerator := 1756472286249469694098412666880 }, { target := 93, numerator := 20888621469762765132264374272 }, { target := 154, numerator := 208432801494529373862881132544 }, { target := 155, numerator := 17526956260638238583262426431488 }, { target := 160, numerator := 17526952032191978576174729134080 }, { target := 168, numerator := 208437029940789380950578429952 }, { target := 492, numerator := 20888197713900596049513283584 }, { target := 493, numerator := 1756472710005331863181163757568 }, { target := 498, numerator := 1756472286249469694098412666880 }, { target := 506, numerator := 20888621469762765132264374272 }, { target := 810, numerator := 4796983193712918875791687680 }, { target := 811, numerator := 708489314164577505131762810880 }, { target := 813, numerator := 7384465634897113258579407667200 }, { target := 821, numerator := 708489314164577505131762810880 }, { target := 828, numerator := 4796983193712918875791687680 }, { target := 845, numerator := 149905724803528714868490240 }, { target := 846, numerator := 22140291067643047035367587840 }, { target := 848, numerator := 230764551090534789330606489600 }, { target := 856, numerator := 22140291067643047035367587840 }, { target := 863, numerator := 149905724803528714868490240 }, { target := 890, numerator := 130824813791615270994837504 }, { target := 891, numerator := 11000959410853407300054417408 }, { target := 896, numerator := 11000956756829229594999521280 }, { target := 904, numerator := 130827467815792976049733632 }, { target := 906, numerator := 172968144004071594079027200 }, { target := 907, numerator := 25546489693434285040808755200 }, { target := 909, numerator := 266266789719847833843007488000 }, { target := 917, numerator := 25546489693434285040808755200 }, { target := 924, numerator := 172968144004071594079027200 }, { target := 941, numerator := 180655617070919220482539520 }, { target := 942, numerator := 26681889235364697709289144320 }, { target := 944, numerator := 278100869262952182013807820800 }, { target := 952, numerator := 26681889235364697709289144320 }, { target := 959, numerator := 180655617070919220482539520 }]

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
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected,
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected,
    Slot12.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 79901495494520619401216000 }, { target := 35, numerator := 6690083094347402758953369600 }, { target := 40, numerator := 6690085515482562433332019200 }, { target := 48, numerator := 79899074359360945022566400 }, { target := 79, numerator := 1342345124307946405940428800 }, { target := 80, numerator := 112393395985036366350416609280 }, { target := 85, numerator := 112393436660107048879977922560 }, { target := 93, numerator := 1342304449237263876379115520 }, { target := 105, numerator := 2908414436000550546204262400 }, { target := 106, numerator := 243519024634245460425902653440 }, { target := 111, numerator := 243519112763565272573285498880 }, { target := 119, numerator := 2908326306680738398821416960 }, { target := 144, numerator := 21609391209104259894231433216 }, { target := 145, numerator := 517231234746947123919991078912 }, { target := 146, numerator := 386877810356544007783820820480 }, { target := 147, numerator := 448917675440746560383388483584 }, { target := 148, numerator := 21609391209104259894231433216 }, { target := 149, numerator := 448220598304969003612606824448 }, { target := 150, numerator := 450311829712301673924951801856 }, { target := 151, numerator := 21609391209104259894231433216 }, { target := 152, numerator := 517231234746947123919991078912 }, { target := 153, numerator := 21609391209104259894231433216 }, { target := 154, numerator := 95881794593424743281459200 }, { target := 155, numerator := 8028099713216883310744043520 }, { target := 160, numerator := 8028102618579074919998423040 }, { target := 168, numerator := 95878889231233134027079680 }, { target := 180, numerator := 1534108713494795892503347200 }, { target := 181, numerator := 128449595411470132971904696320 }, { target := 186, numerator := 128449641897265198719974768640 }, { target := 194, numerator := 1534062227699730144433274880 }, { target := 215, numerator := 111862093692328867161702400 }, { target := 216, numerator := 9366116332086363862534717440 }, { target := 221, numerator := 9366119721675587406664826880 }, { target := 229, numerator := 111858704103105323031592960 }, { target := 295, numerator := 2908414436000550546204262400 }, { target := 296, numerator := 243519024634245460425902653440 }, { target := 301, numerator := 243519112763565272573285498880 }, { target := 309, numerator := 2908326306680738398821416960 }, { target := 321, numerator := 2908414436000550546204262400 }, { target := 322, numerator := 243519024634245460425902653440 }, { target := 327, numerator := 243519112763565272573285498880 }, { target := 335, numerator := 2908326306680738398821416960 }, { target := 370, numerator := 1534108713494795892503347200 }, { target := 371, numerator := 128449595411470132971904696320 }, { target := 376, numerator := 128449641897265198719974768640 }, { target := 384, numerator := 1534062227699730144433274880 }, { target := 396, numerator := 35891751776138662235026227200 }, { target := 397, numerator := 3005185325980853319321853624320 }, { target := 402, numerator := 3005186413554767045052743024640 }, { target := 410, numerator := 35890664202224936504136826880 }, { target := 431, numerator := 2876453837802742298443776000 }, { target := 432, numerator := 240842991396506499322321305600 }, { target := 437, numerator := 240843078557372247599952691200 }, { target := 445, numerator := 2876366676936994020812390400 }, { target := 482, numerator := 576815432463414719976308736 }, { target := 483, numerator := 13806356480253345878142615552 }, { target := 484, numerator := 10326856936038553857640366080 }, { target := 485, numerator := 11982875435691583214991704064 }, { target := 486, numerator := 576815432463414719976308736 }, { target := 487, numerator := 11964268486257279514347307008 }, { target := 488, numerator := 12020089334560190616280498176 }, { target := 489, numerator := 576815432463414719976308736 }, { target := 490, numerator := 13806356480253345878142615552 }, { target := 491, numerator := 576815432463414719976308736 }]

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
    Slot12.Left11.expected,
    Slot12.Left12.expected,
    Slot12.Left13.expected,
    Slot12.Left14.expected,
    Slot12.Left15.expected,
    Slot12.Left16.expected,
    Slot12.Left17.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 28108970350183886423353982976 }, { target := 2, numerator := 28108970350183886423353982976 }, { target := 3, numerator := 28108970350183886423353982976 }, { target := 4, numerator := 28108970350183886423353982976 }, { target := 10, numerator := 3574977984932403213112442880 }, { target := 12, numerator := 34627498041467741278683791360 }, { target := 17, numerator := 3574977984932403213112442880 }, { target := 51, numerator := 102238384328160902340379934720 }, { target := 52, numerator := 102238384328160902340379934720 }, { target := 53, numerator := 102238384328160902340379934720 }, { target := 54, numerator := 102238384328160902340379934720 }, { target := 55, numerator := 132019180863670636343879270400 }, { target := 57, numerator := 1278747434546612931478211788800 }, { target := 62, numerator := 132019180863670636343879270400 }, { target := 140, numerator := 28108970350183886423353982976 }, { target := 141, numerator := 28108970350183886423353982976 }, { target := 142, numerator := 28108970350183886423353982976 }, { target := 143, numerator := 28108970350183886423353982976 }, { target := 144, numerator := 132019148535503949188384686080 }, { target := 146, numerator := 1278747121413627676217583861760 }, { target := 151, numerator := 132019148535503949188384686080 }, { target := 482, numerator := 3575010313099090368607027200 }, { target := 484, numerator := 34627811174452996539311718400 }, { target := 489, numerator := 3575010313099090368607027200 }, { target := 492, numerator := 1342345124307946405940428800 }, { target := 493, numerator := 112393395985036366350416609280 }, { target := 498, numerator := 112393436660107048879977922560 }, { target := 506, numerator := 1342304449237263876379115520 }, { target := 527, numerator := 2908414436000550546204262400 }, { target := 528, numerator := 243519024634245460425902653440 }, { target := 533, numerator := 243519112763565272573285498880 }, { target := 541, numerator := 2908326306680738398821416960 }, { target := 637, numerator := 111862093692328867161702400 }, { target := 638, numerator := 9366116332086363862534717440 }, { target := 643, numerator := 9366119721675587406664826880 }, { target := 651, numerator := 111858704103105323031592960 }, { target := 663, numerator := 2876453837802742298443776000 }, { target := 664, numerator := 240842991396506499322321305600 }, { target := 669, numerator := 240843078557372247599952691200 }, { target := 677, numerator := 2876366676936994020812390400 }, { target := 698, numerator := 111862093692328867161702400 }, { target := 699, numerator := 9366116332086363862534717440 }, { target := 704, numerator := 9366119721675587406664826880 }, { target := 712, numerator := 111858704103105323031592960 }, { target := 759, numerator := 2908414436000550546204262400 }, { target := 760, numerator := 243519024634245460425902653440 }, { target := 765, numerator := 243519112763565272573285498880 }, { target := 773, numerator := 2908326306680738398821416960 }, { target := 794, numerator := 2908414436000550546204262400 }, { target := 795, numerator := 243519024634245460425902653440 }, { target := 800, numerator := 243519112763565272573285498880 }, { target := 808, numerator := 2908326306680738398821416960 }, { target := 890, numerator := 95881794593424743281459200 }, { target := 891, numerator := 8028099713216883310744043520 }, { target := 896, numerator := 8028102618579074919998423040 }, { target := 904, numerator := 95878889231233134027079680 }]

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
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left2.expected,
    Slot15.Left3.expected,
    Slot15.Left4.expected,
    Slot15.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 11333679558887148512870400 }, { target := 11, numerator := 227126938360098456197922816 }, { target := 12, numerator := 381264980360963675972960256 }, { target := 13, numerator := 365851176160877153995456512 }, { target := 14, numerator := 11333679558887148512870400 }, { target := 15, numerator := 365851176160877153995456512 }, { target := 16, numerator := 244354131289606921937485824 }, { target := 17, numerator := 11787026741242634453385216 }, { target := 18, numerator := 227126938360098456197922816 }, { target := 19, numerator := 10880332376531662572355584 }, { target := 24, numerator := 13458744476178488859033600 }, { target := 25, numerator := 269713239302616916735033344 }, { target := 26, numerator := 452752164178644365217890304 }, { target := 27, numerator := 434448271691041620369604608 }, { target := 28, numerator := 13458744476178488859033600 }, { target := 29, numerator := 434448271691041620369604608 }, { target := 30, numerator := 290170530906408219800764416 }, { target := 31, numerator := 13997094255225628413394944 }, { target := 32, numerator := 269713239302616916735033344 }, { target := 33, numerator := 12920394697131349304672256 }, { target := 55, numerator := 10271147100241478339788800 }, { target := 56, numerator := 205833787888839225929367552 }, { target := 57, numerator := 345521388452123331350495232 }, { target := 58, numerator := 331552628395794920808382464 }, { target := 59, numerator := 10271147100241478339788800 }, { target := 60, numerator := 331552628395794920808382464 }, { target := 61, numerator := 221445931481206273005846528 }, { target := 62, numerator := 10681992984251137473380352 }, { target := 63, numerator := 205833787888839225929367552 }, { target := 64, numerator := 9860301216231819206197248 }, { target := 69, numerator := 105899068378351793917132800 }, { target := 70, numerator := 2122217330302169950099341312 }, { target := 71, numerator := 3562444660247754347372347392 }, { target := 72, numerator := 3418421927253195907645046784 }, { target := 73, numerator := 105899068378351793917132800 }, { target := 74, numerator := 3418421927253195907645046784 }, { target := 75, numerator := 2283183914237264676853383168 }, { target := 76, numerator := 110135031113485865673818112 }, { target := 77, numerator := 2122217330302169950099341312 }, { target := 78, numerator := 101663105643217722160447488 }, { target := 95, numerator := 12750389503748042076979200 }, { target := 96, numerator := 255517805655110763222663168 }, { target := 97, numerator := 428923102906084135469580288 }, { target := 98, numerator := 411582573180986798244888576 }, { target := 99, numerator := 12750389503748042076979200 }, { target := 100, numerator := 411582573180986798244888576 }, { target := 101, numerator := 274898397700807787179671552 }, { target := 102, numerator := 13260405083897963760058368 }, { target := 103, numerator := 255517805655110763222663168 }, { target := 104, numerator := 12240373923598120393900032 }, { target := 144, numerator := 10271147100241478339788800 }, { target := 145, numerator := 205833787888839225929367552 }, { target := 146, numerator := 345521388452123331350495232 }, { target := 147, numerator := 331552628395794920808382464 }, { target := 148, numerator := 10271147100241478339788800 }, { target := 149, numerator := 331552628395794920808382464 }, { target := 150, numerator := 221445931481206273005846528 }, { target := 151, numerator := 10681992984251137473380352 }, { target := 152, numerator := 205833787888839225929367552 }, { target := 153, numerator := 9860301216231819206197248 }]

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
    Slot15.Left6.expected,
    Slot15.Left7.expected,
    Slot15.Left8.expected,
    Slot15.Left9.expected,
    Slot15.Left10.expected,
    Slot15.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 170, numerator := 12750389503748042076979200 }, { target := 171, numerator := 255517805655110763222663168 }, { target := 172, numerator := 428923102906084135469580288 }, { target := 173, numerator := 411582573180986798244888576 }, { target := 174, numerator := 12750389503748042076979200 }, { target := 175, numerator := 411582573180986798244888576 }, { target := 176, numerator := 274898397700807787179671552 }, { target := 177, numerator := 13260405083897963760058368 }, { target := 178, numerator := 255517805655110763222663168 }, { target := 179, numerator := 12240373923598120393900032 }, { target := 271, numerator := 12750389503748042076979200 }, { target := 272, numerator := 255517805655110763222663168 }, { target := 273, numerator := 428923102906084135469580288 }, { target := 274, numerator := 411582573180986798244888576 }, { target := 275, numerator := 12750389503748042076979200 }, { target := 276, numerator := 411582573180986798244888576 }, { target := 277, numerator := 274898397700807787179671552 }, { target := 278, numerator := 13260405083897963760058368 }, { target := 279, numerator := 255517805655110763222663168 }, { target := 280, numerator := 12240373923598120393900032 }, { target := 285, numerator := 546141683743874468963942400 }, { target := 286, numerator := 10944679342227244358037405696 }, { target := 287, numerator := 18372206241143937135947022336 }, { target := 288, numerator := 17629453551252267858156060672 }, { target := 289, numerator := 546141683743874468963942400 }, { target := 290, numerator := 17629453551252267858156060672 }, { target := 291, numerator := 11774814701517933550862598144 }, { target := 292, numerator := 567987351093629447722500096 }, { target := 293, numerator := 10944679342227244358037405696 }, { target := 294, numerator := 524296016394119490205384704 }, { target := 311, numerator := 12750389503748042076979200 }, { target := 312, numerator := 255517805655110763222663168 }, { target := 313, numerator := 428923102906084135469580288 }, { target := 314, numerator := 411582573180986798244888576 }, { target := 315, numerator := 12750389503748042076979200 }, { target := 316, numerator := 411582573180986798244888576 }, { target := 317, numerator := 274898397700807787179671552 }, { target := 318, numerator := 13260405083897963760058368 }, { target := 319, numerator := 255517805655110763222663168 }, { target := 320, numerator := 12240373923598120393900032 }, { target := 360, numerator := 105899068378351793917132800 }, { target := 361, numerator := 2122217330302169950099341312 }, { target := 362, numerator := 3562444660247754347372347392 }, { target := 363, numerator := 3418421927253195907645046784 }, { target := 364, numerator := 105899068378351793917132800 }, { target := 365, numerator := 3418421927253195907645046784 }, { target := 366, numerator := 2283183914237264676853383168 }, { target := 367, numerator := 110135031113485865673818112 }, { target := 368, numerator := 2122217330302169950099341312 }, { target := 369, numerator := 101663105643217722160447488 }, { target := 386, numerator := 546141683743874468963942400 }, { target := 387, numerator := 10944679342227244358037405696 }, { target := 388, numerator := 18372206241143937135947022336 }, { target := 389, numerator := 17629453551252267858156060672 }, { target := 390, numerator := 546141683743874468963942400 }, { target := 391, numerator := 17629453551252267858156060672 }, { target := 392, numerator := 11774814701517933550862598144 }, { target := 393, numerator := 567987351093629447722500096 }, { target := 394, numerator := 10944679342227244358037405696 }, { target := 395, numerator := 524296016394119490205384704 }]

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
    Slot15.Left12.expected,
    Slot15.Left13.expected,
    Slot15.Left14.expected,
    Slot15.Left15.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 39614081257132168796771975168 }, { target := 1, numerator := 3710812420045939657366568960 }, { target := 2, numerator := 3391751912901802789630377984 }, { target := 3, numerator := 3710812420045939657366568960 }, { target := 4, numerator := 3391751912901802789630377984 }, { target := 50, numerator := 39614081257132168796771975168 }, { target := 51, numerator := 13275186425336582085562859520 }, { target := 52, numerator := 12133768527083343252037828608 }, { target := 53, numerator := 13275186425336582085562859520 }, { target := 54, numerator := 12133768527083343252037828608 }, { target := 140, numerator := 3710811186419929728040304640 }, { target := 141, numerator := 3391750785344571284134035456 }, { target := 142, numerator := 3710811186419929728040304640 }, { target := 143, numerator := 3391750785344571284134035456 }, { target := 482, numerator := 11333679558887148512870400 }, { target := 483, numerator := 227126938360098456197922816 }, { target := 484, numerator := 381264980360963675972960256 }, { target := 485, numerator := 365851176160877153995456512 }, { target := 486, numerator := 11333679558887148512870400 }, { target := 487, numerator := 365851176160877153995456512 }, { target := 488, numerator := 244354131289606921937485824 }, { target := 489, numerator := 11787026741242634453385216 }, { target := 490, numerator := 227126938360098456197922816 }, { target := 491, numerator := 10880332376531662572355584 }, { target := 627, numerator := 12750389503748042076979200 }, { target := 628, numerator := 255517805655110763222663168 }, { target := 629, numerator := 428923102906084135469580288 }, { target := 630, numerator := 411582573180986798244888576 }, { target := 631, numerator := 12750389503748042076979200 }, { target := 632, numerator := 411582573180986798244888576 }, { target := 633, numerator := 274898397700807787179671552 }, { target := 634, numerator := 13260405083897963760058368 }, { target := 635, numerator := 255517805655110763222663168 }, { target := 636, numerator := 12240373923598120393900032 }, { target := 653, numerator := 12750389503748042076979200 }, { target := 654, numerator := 255517805655110763222663168 }, { target := 655, numerator := 428923102906084135469580288 }, { target := 656, numerator := 411582573180986798244888576 }, { target := 657, numerator := 12750389503748042076979200 }, { target := 658, numerator := 411582573180986798244888576 }, { target := 659, numerator := 274898397700807787179671552 }, { target := 660, numerator := 13260405083897963760058368 }, { target := 661, numerator := 255517805655110763222663168 }, { target := 662, numerator := 12240373923598120393900032 }, { target := 749, numerator := 13458744476178488859033600 }, { target := 750, numerator := 269713239302616916735033344 }, { target := 751, numerator := 452752164178644365217890304 }, { target := 752, numerator := 434448271691041620369604608 }, { target := 753, numerator := 13458744476178488859033600 }, { target := 754, numerator := 434448271691041620369604608 }, { target := 755, numerator := 290170530906408219800764416 }, { target := 756, numerator := 13997094255225628413394944 }, { target := 757, numerator := 269713239302616916735033344 }, { target := 758, numerator := 12920394697131349304672256 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent1
