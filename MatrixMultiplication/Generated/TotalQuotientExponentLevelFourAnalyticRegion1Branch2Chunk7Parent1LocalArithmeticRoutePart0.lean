import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 31; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent1

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
    Slot3.Left4.expected,
    Slot3.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 7906857496279933320859484160 }, { target := 202, numerator := 297080948276098714874014597120 }, { target := 205, numerator := 297058479415476388737832714240 }, { target := 212, numerator := 7929326356902259457041367040 }, { target := 296, numerator := 8132767710459359987169755136 }, { target := 298, numerator := 305568975369701535298986442752 }, { target := 301, numerator := 305545864541632856987485077504 }, { target := 308, numerator := 8155878538528038298671120384 }, { target := 331, numerator := 7906857496279933320859484160 }, { target := 333, numerator := 297080948276098714874014597120 }, { target := 336, numerator := 297058479415476388737832714240 }, { target := 343, numerator := 7929326356902259457041367040 }, { target := 347, numerator := 7387746910373479788314624000 }, { target := 350, numerator := 25360843390458729023615795200 }, { target := 352, numerator := 7387746910373479788314624000 }, { target := 467, numerator := 7003216639562226655618400256 }, { target := 469, numerator := 263128839901687433174127214592 }, { target := 472, numerator := 263108938910850515739223261184 }, { target := 479, numerator := 7023117630399144090522353664 }, { target := 563, numerator := 327795720774348092816203186176 }, { target := 565, numerator := 12316127312817692436634148012032 }, { target := 568, numerator := 12315195818053035430245579096064 }, { target := 575, numerator := 328727215539005099204772102144 }, { target := 598, numerator := 89234534600873533192557035520 }, { target := 600, numerator := 3352770701973114067863879024640 }, { target := 603, numerator := 3352517124831804958612683489280 }, { target := 610, numerator := 89488111742182642443752570880 }, { target := 614, numerator := 148050448083884534957825064960 }, { target := 617, numerator := 508231301544792929633260535808 }, { target := 619, numerator := 148050448083884534957825064960 }, { target := 710, numerator := 248523806064963860078903951360 }, { target := 713, numerator := 853138771655031644354435350528 }, { target := 715, numerator := 248523806064963860078903951360 }, { target := 736, numerator := 238476470266855927566796062720 }, { target := 739, numerator := 818648024644007772882317869056 }, { target := 741, numerator := 238476470266855927566796062720 }, { target := 746, numerator := 41393620063604902941939466240 }, { target := 748, numerator := 41393620063604902941939466240 }, { target := 881, numerator := 7387746910373479788314624000 }, { target := 884, numerator := 25360843390458729023615795200 }, { target := 886, numerator := 7387746910373479788314624000 }, { target := 977, numerator := 238476470266855927566796062720 }, { target := 980, numerator := 818648024644007772882317869056 }, { target := 982, numerator := 238476470266855927566796062720 }, { target := 1003, numerator := 159279823387652224236063293440 }, { target := 1006, numerator := 546779783498290197749156544512 }, { target := 1008, numerator := 159279823387652224236063293440 }, { target := 1013, numerator := 37834542450659434651604484096 }, { target := 1015, numerator := 37834542450659434651604484096 }, { target := 1052, numerator := 7683256786788418979847208960 }, { target := 1055, numerator := 26375277126077078184560427008 }, { target := 1057, numerator := 7683256786788418979847208960 }, { target := 1078, numerator := 148050448083884534957825064960 }, { target := 1081, numerator := 508231301544792929633260535808 }, { target := 1083, numerator := 148050448083884534957825064960 }, { target := 1088, numerator := 41393620063604902941939466240 }, { target := 1090, numerator := 41393620063604902941939466240 }, { target := 1092, numerator := 7092237033958540596782039040 }, { target := 1095, numerator := 24346409654840379862671163392 }, { target := 1097, numerator := 7092237033958540596782039040 }, { target := 1102, numerator := 37834542450659434651604484096 }, { target := 1104, numerator := 37834542450659434651604484096 }]

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
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 35647631946168907534958592 }, { target := 72, numerator := 5691044379531987065235308544 }, { target := 74, numerator := 56788064710157343961229819904 }, { target := 82, numerator := 5691044379531987065235308544 }, { target := 89, numerator := 35643564439100654578827264 }, { target := 146, numerator := 950603518564504200932229120 }, { target := 147, numerator := 151761183454186321739608227840 }, { target := 149, numerator := 1514348392270862505632795197440 }, { target := 157, numerator := 151761183454186321739608227840 }, { target := 164, numerator := 950495051709350788768727040 }, { target := 181, numerator := 909014614627307142141444096 }, { target := 182, numerator := 145121631678065670163500367872 }, { target := 184, numerator := 1448095650109012271011360407552 }, { target := 192, numerator := 145121631678065670163500367872 }, { target := 199, numerator := 908910893197066691760095232 }, { target := 242, numerator := 29706359955140756279132160 }, { target := 243, numerator := 4742536982943322554362757120 }, { target := 245, numerator := 47323387258464453301024849920 }, { target := 253, numerator := 4742536982943322554362757120 }, { target := 260, numerator := 29702970365917212149022720 }, { target := 659, numerator := 8132767710459359987169755136 }, { target := 661, numerator := 305568975369701535298986442752 }, { target := 664, numerator := 305545864541632856987485077504 }, { target := 671, numerator := 8155878538528038298671120384 }, { target := 694, numerator := 327795720774348092816203186176 }, { target := 696, numerator := 12316127312817692436634148012032 }, { target := 699, numerator := 12315195818053035430245579096064 }, { target := 706, numerator := 328727215539005099204772102144 }, { target := 720, numerator := 7906857496279933320859484160 }, { target := 722, numerator := 297080948276098714874014597120 }, { target := 725, numerator := 297058479415476388737832714240 }, { target := 732, numerator := 7929326356902259457041367040 }, { target := 830, numerator := 7906857496279933320859484160 }, { target := 832, numerator := 297080948276098714874014597120 }, { target := 835, numerator := 297058479415476388737832714240 }, { target := 842, numerator := 7929326356902259457041367040 }, { target := 865, numerator := 6777306425382799989308129280 }, { target := 867, numerator := 254640812808084612749155368960 }, { target := 870, numerator := 254621553784694047489570897920 }, { target := 877, numerator := 6796565448773365248892600320 }, { target := 926, numerator := 7906857496279933320859484160 }, { target := 928, numerator := 297080948276098714874014597120 }, { target := 931, numerator := 297058479415476388737832714240 }, { target := 938, numerator := 7929326356902259457041367040 }, { target := 961, numerator := 89234534600873533192557035520 }, { target := 963, numerator := 3352770701973114067863879024640 }, { target := 966, numerator := 3352517124831804958612683489280 }, { target := 973, numerator := 89488111742182642443752570880 }, { target := 987, numerator := 6777306425382799989308129280 }, { target := 989, numerator := 254640812808084612749155368960 }, { target := 992, numerator := 254621553784694047489570897920 }, { target := 999, numerator := 6796565448773365248892600320 }, { target := 1036, numerator := 7906857496279933320859484160 }, { target := 1038, numerator := 297080948276098714874014597120 }, { target := 1041, numerator := 297058479415476388737832714240 }, { target := 1048, numerator := 7929326356902259457041367040 }, { target := 1062, numerator := 7003216639562226655618400256 }, { target := 1064, numerator := 263128839901687433174127214592 }, { target := 1067, numerator := 263108938910850515739223261184 }, { target := 1074, numerator := 7023117630399144090522353664 }]

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
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 277, numerator := 932779702591419747164749824 }, { target := 278, numerator := 148915661264420328206990573568 }, { target := 280, numerator := 1485954359915783833652180287488 }, { target := 288, numerator := 148915661264420328206990573568 }, { target := 295, numerator := 932673269489800461479313408 }, { target := 312, numerator := 29706359955140756279132160 }, { target := 313, numerator := 4742536982943322554362757120 }, { target := 315, numerator := 47323387258464453301024849920 }, { target := 323, numerator := 4742536982943322554362757120 }, { target := 330, numerator := 29702970365917212149022720 }, { target := 413, numerator := 909014614627307142141444096 }, { target := 414, numerator := 145121631678065670163500367872 }, { target := 416, numerator := 1448095650109012271011360407552 }, { target := 424, numerator := 145121631678065670163500367872 }, { target := 431, numerator := 908910893197066691760095232 }, { target := 448, numerator := 516890663219449159256899584 }, { target := 449, numerator := 82520143503213812445911973888 }, { target := 451, numerator := 823426938297281487437832388608 }, { target := 459, numerator := 82520143503213812445911973888 }, { target := 466, numerator := 516831684366959491392995328 }, { target := 509, numerator := 932779702591419747164749824 }, { target := 510, numerator := 148915661264420328206990573568 }, { target := 512, numerator := 1485954359915783833652180287488 }, { target := 520, numerator := 148915661264420328206990573568 }, { target := 527, numerator := 932673269489800461479313408 }, { target := 544, numerator := 14562057650009998728030584832 }, { target := 545, numerator := 2324791629038816716148623540224 }, { target := 547, numerator := 23197924434099275008162381430784 }, { target := 555, numerator := 2324791629038816716148623540224 }, { target := 562, numerator := 14560396073372617395450937344 }, { target := 579, numerator := 570362111138702520559337472 }, { target := 580, numerator := 91056710072511793043764936704 }, { target := 582, numerator := 908609035362517503379677118464 }, { target := 590, numerator := 91056710072511793043764936704 }, { target := 597, numerator := 570297031025610473261236224 }, { target := 640, numerator := 950603518564504200932229120 }, { target := 641, numerator := 151761183454186321739608227840 }, { target := 643, numerator := 1514348392270862505632795197440 }, { target := 651, numerator := 151761183454186321739608227840 }, { target := 658, numerator := 950495051709350788768727040 }, { target := 675, numerator := 909014614627307142141444096 }, { target := 676, numerator := 145121631678065670163500367872 }, { target := 678, numerator := 1448095650109012271011360407552 }, { target := 686, numerator := 145121631678065670163500367872 }, { target := 693, numerator := 908910893197066691760095232 }, { target := 776, numerator := 29706359955140756279132160 }, { target := 777, numerator := 4742536982943322554362757120 }, { target := 779, numerator := 47323387258464453301024849920 }, { target := 787, numerator := 4742536982943322554362757120 }, { target := 794, numerator := 29702970365917212149022720 }, { target := 811, numerator := 570362111138702520559337472 }, { target := 812, numerator := 91056710072511793043764936704 }, { target := 814, numerator := 908609035362517503379677118464 }, { target := 822, numerator := 91056710072511793043764936704 }, { target := 829, numerator := 570297031025610473261236224 }, { target := 846, numerator := 29706359955140756279132160 }, { target := 847, numerator := 4742536982943322554362757120 }, { target := 849, numerator := 47323387258464453301024849920 }, { target := 857, numerator := 4742536982943322554362757120 }, { target := 864, numerator := 29702970365917212149022720 }]

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
    Slot4.Left16.expected,
    Slot4.Left17.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 234607166868963974216417280 }, { target := 30, numerator := 182472240898083091057213440 }, { target := 31, numerator := 208539703883523532636815360 }, { target := 32, numerator := 245034152063140150848258048 }, { target := 33, numerator := 2893488391383889015335813120 }, { target := 34, numerator := 6506438761165934218268639232 }, { target := 35, numerator := 182472240898083091057213440 }, { target := 36, numerator := 2893488391383889015335813120 }, { target := 37, numerator := 208539703883523532636815360 }, { target := 38, numerator := 203326211286435444320894976 }, { target := 39, numerator := 203326211286435444320894976 }, { target := 40, numerator := 203326211286435444320894976 }, { target := 41, numerator := 6506438761165934218268639232 }, { target := 42, numerator := 203326211286435444320894976 }, { target := 43, numerator := 234607166868963974216417280 }, { target := 44, numerator := 245034152063140150848258048 }, { target := 55, numerator := 229719517559193891420241920 }, { target := 56, numerator := 178670735879373026660188160 }, { target := 57, numerator := 204195126719283459040215040 }, { target := 58, numerator := 239929273895158064372252672 }, { target := 59, numerator := 2833207383230057994182983680 }, { target := 60, numerator := 6370887953641643922054709248 }, { target := 61, numerator := 178670735879373026660188160 }, { target := 62, numerator := 2833207383230057994182983680 }, { target := 63, numerator := 204195126719283459040215040 }, { target := 64, numerator := 199090248551301372564209664 }, { target := 65, numerator := 199090248551301372564209664 }, { target := 66, numerator := 199090248551301372564209664 }, { target := 67, numerator := 6370887953641643922054709248 }, { target := 68, numerator := 199090248551301372564209664 }, { target := 69, numerator := 229719517559193891420241920 }, { target := 70, numerator := 239929273895158064372252672 }, { target := 104, numerator := 180843024461493063458488320 }, { target := 105, numerator := 140655685692272382689935360 }, { target := 106, numerator := 160749355076882723074211840 }, { target := 107, numerator := 188880492215337199612198912 }, { target := 108, numerator := 2230397301691747782654689280 }, { target := 109, numerator := 5015379878398740959915409408 }, { target := 110, numerator := 140655685692272382689935360 }, { target := 111, numerator := 2230397301691747782654689280 }, { target := 112, numerator := 160749355076882723074211840 }, { target := 113, numerator := 156730621199960654997356544 }, { target := 114, numerator := 156730621199960654997356544 }, { target := 115, numerator := 156730621199960654997356544 }, { target := 116, numerator := 5015379878398740959915409408 }, { target := 117, numerator := 156730621199960654997356544 }, { target := 118, numerator := 180843024461493063458488320 }, { target := 119, numerator := 188880492215337199612198912 }, { target := 907, numerator := 914955886618335293397270528 }, { target := 908, numerator := 146070139074654334674372919296 }, { target := 910, numerator := 1457560327560705161671565377536 }, { target := 918, numerator := 146070139074654334674372919296 }, { target := 925, numerator := 914851487270250134189899776 }, { target := 942, numerator := 516890663219449159256899584 }, { target := 943, numerator := 82520143503213812445911973888 }, { target := 945, numerator := 823426938297281487437832388608 }, { target := 953, numerator := 82520143503213812445911973888 }, { target := 960, numerator := 516831684366959491392995328 }, { target := 1017, numerator := 35647631946168907534958592 }, { target := 1018, numerator := 5691044379531987065235308544 }, { target := 1020, numerator := 56788064710157343961229819904 }, { target := 1028, numerator := 5691044379531987065235308544 }, { target := 1035, numerator := 35643564439100654578827264 }]

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
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 130, numerator := 5684336147262606291951943680 }, { target := 131, numerator := 4421150336759804893740400640 }, { target := 132, numerator := 5052743242011205592846172160 }, { target := 133, numerator := 5936973309363166571594252288 }, { target := 134, numerator := 70106812482905477600740638720 }, { target := 135, numerator := 157645589150749614496800571392 }, { target := 136, numerator := 4421150336759804893740400640 }, { target := 137, numerator := 70106812482905477600740638720 }, { target := 138, numerator := 5052743242011205592846172160 }, { target := 139, numerator := 4926424660960925453025017856 }, { target := 140, numerator := 4926424660960925453025017856 }, { target := 141, numerator := 4926424660960925453025017856 }, { target := 142, numerator := 157645589150749614496800571392 }, { target := 143, numerator := 4926424660960925453025017856 }, { target := 144, numerator := 5684336147262606291951943680 }, { target := 145, numerator := 5936973309363166571594252288 }, { target := 165, numerator := 180843024461493063458488320 }, { target := 166, numerator := 140655685692272382689935360 }, { target := 167, numerator := 160749355076882723074211840 }, { target := 168, numerator := 188880492215337199612198912 }, { target := 169, numerator := 2230397301691747782654689280 }, { target := 170, numerator := 5015379878398740959915409408 }, { target := 171, numerator := 140655685692272382689935360 }, { target := 172, numerator := 2230397301691747782654689280 }, { target := 173, numerator := 160749355076882723074211840 }, { target := 174, numerator := 156730621199960654997356544 }, { target := 175, numerator := 156730621199960654997356544 }, { target := 176, numerator := 156730621199960654997356544 }, { target := 177, numerator := 5015379878398740959915409408 }, { target := 178, numerator := 156730621199960654997356544 }, { target := 179, numerator := 180843024461493063458488320 }, { target := 180, numerator := 188880492215337199612198912 }, { target := 226, numerator := 180843024461493063458488320 }, { target := 227, numerator := 140655685692272382689935360 }, { target := 228, numerator := 160749355076882723074211840 }, { target := 229, numerator := 188880492215337199612198912 }, { target := 230, numerator := 2230397301691747782654689280 }, { target := 231, numerator := 5015379878398740959915409408 }, { target := 232, numerator := 140655685692272382689935360 }, { target := 233, numerator := 2230397301691747782654689280 }, { target := 234, numerator := 160749355076882723074211840 }, { target := 235, numerator := 156730621199960654997356544 }, { target := 236, numerator := 156730621199960654997356544 }, { target := 237, numerator := 156730621199960654997356544 }, { target := 238, numerator := 5015379878398740959915409408 }, { target := 239, numerator := 156730621199960654997356544 }, { target := 240, numerator := 180843024461493063458488320 }, { target := 241, numerator := 188880492215337199612198912 }, { target := 261, numerator := 185730673771263146254663680 }, { target := 262, numerator := 144457190710982447086960640 }, { target := 263, numerator := 165093932241122796670812160 }, { target := 264, numerator := 193985370383319286088204288 }, { target := 265, numerator := 2290678309845578803807518720 }, { target := 266, numerator := 5150930685923031256129339392 }, { target := 267, numerator := 144457190710982447086960640 }, { target := 268, numerator := 2290678309845578803807518720 }, { target := 269, numerator := 165093932241122796670812160 }, { target := 270, numerator := 160966583935094726754041856 }, { target := 271, numerator := 160966583935094726754041856 }, { target := 272, numerator := 160966583935094726754041856 }, { target := 273, numerator := 5150930685923031256129339392 }, { target := 274, numerator := 160966583935094726754041856 }, { target := 275, numerator := 185730673771263146254663680 }, { target := 276, numerator := 193985370383319286088204288 }]

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
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot5.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 371, numerator := 185730673771263146254663680 }, { target := 372, numerator := 144457190710982447086960640 }, { target := 373, numerator := 165093932241122796670812160 }, { target := 374, numerator := 193985370383319286088204288 }, { target := 375, numerator := 2290678309845578803807518720 }, { target := 376, numerator := 5150930685923031256129339392 }, { target := 377, numerator := 144457190710982447086960640 }, { target := 378, numerator := 2290678309845578803807518720 }, { target := 379, numerator := 165093932241122796670812160 }, { target := 380, numerator := 160966583935094726754041856 }, { target := 381, numerator := 160966583935094726754041856 }, { target := 382, numerator := 160966583935094726754041856 }, { target := 383, numerator := 5150930685923031256129339392 }, { target := 384, numerator := 160966583935094726754041856 }, { target := 385, numerator := 185730673771263146254663680 }, { target := 386, numerator := 193985370383319286088204288 }, { target := 397, numerator := 3142758506182163237940756480 }, { target := 398, numerator := 2444367727030571407287255040 }, { target := 399, numerator := 2793563116606367322614005760 }, { target := 400, numerator := 3282436662012481604071456768 }, { target := 401, numerator := 38760688242913346601269329920 }, { target := 402, numerator := 87159169238118660465556979712 }, { target := 403, numerator := 2444367727030571407287255040 }, { target := 404, numerator := 38760688242913346601269329920 }, { target := 405, numerator := 2793563116606367322614005760 }, { target := 406, numerator := 2723724038691208139548655616 }, { target := 407, numerator := 2723724038691208139548655616 }, { target := 408, numerator := 2723724038691208139548655616 }, { target := 409, numerator := 87159169238118660465556979712 }, { target := 410, numerator := 2723724038691208139548655616 }, { target := 411, numerator := 3142758506182163237940756480 }, { target := 412, numerator := 3282436662012481604071456768 }, { target := 432, numerator := 171067725841952897866137600 }, { target := 433, numerator := 133052675654852253895884800 }, { target := 434, numerator := 152060200748402575881011200 }, { target := 435, numerator := 178670735879373026660188160 }, { target := 436, numerator := 2109835285384085740349030400 }, { target := 437, numerator := 4744278263350160367487549440 }, { target := 438, numerator := 133052675654852253895884800 }, { target := 439, numerator := 2109835285384085740349030400 }, { target := 440, numerator := 152060200748402575881011200 }, { target := 441, numerator := 148258695729692511483985920 }, { target := 442, numerator := 148258695729692511483985920 }, { target := 443, numerator := 148258695729692511483985920 }, { target := 444, numerator := 4744278263350160367487549440 }, { target := 445, numerator := 148258695729692511483985920 }, { target := 446, numerator := 171067725841952897866137600 }, { target := 447, numerator := 178670735879373026660188160 }, { target := 493, numerator := 5684336147262606291951943680 }, { target := 494, numerator := 4421150336759804893740400640 }, { target := 495, numerator := 5052743242011205592846172160 }, { target := 496, numerator := 5936973309363166571594252288 }, { target := 497, numerator := 70106812482905477600740638720 }, { target := 498, numerator := 157645589150749614496800571392 }, { target := 499, numerator := 4421150336759804893740400640 }, { target := 500, numerator := 70106812482905477600740638720 }, { target := 501, numerator := 5052743242011205592846172160 }, { target := 502, numerator := 4926424660960925453025017856 }, { target := 503, numerator := 4926424660960925453025017856 }, { target := 504, numerator := 4926424660960925453025017856 }, { target := 505, numerator := 157645589150749614496800571392 }, { target := 506, numerator := 4926424660960925453025017856 }, { target := 507, numerator := 5684336147262606291951943680 }, { target := 508, numerator := 5936973309363166571594252288 }]

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
    Slot5.Left11.expected,
    Slot5.Left12.expected,
    Slot5.Left13.expected,
    Slot5.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 528, numerator := 3142758506182163237940756480 }, { target := 529, numerator := 2444367727030571407287255040 }, { target := 530, numerator := 2793563116606367322614005760 }, { target := 531, numerator := 3282436662012481604071456768 }, { target := 532, numerator := 38760688242913346601269329920 }, { target := 533, numerator := 87159169238118660465556979712 }, { target := 534, numerator := 2444367727030571407287255040 }, { target := 535, numerator := 38760688242913346601269329920 }, { target := 536, numerator := 2793563116606367322614005760 }, { target := 537, numerator := 2723724038691208139548655616 }, { target := 538, numerator := 2723724038691208139548655616 }, { target := 539, numerator := 2723724038691208139548655616 }, { target := 540, numerator := 87159169238118660465556979712 }, { target := 541, numerator := 2723724038691208139548655616 }, { target := 542, numerator := 3142758506182163237940756480 }, { target := 543, numerator := 3282436662012481604071456768 }, { target := 624, numerator := 234607166868963974216417280 }, { target := 625, numerator := 182472240898083091057213440 }, { target := 626, numerator := 208539703883523532636815360 }, { target := 627, numerator := 245034152063140150848258048 }, { target := 628, numerator := 2893488391383889015335813120 }, { target := 629, numerator := 6506438761165934218268639232 }, { target := 630, numerator := 182472240898083091057213440 }, { target := 631, numerator := 2893488391383889015335813120 }, { target := 632, numerator := 208539703883523532636815360 }, { target := 633, numerator := 203326211286435444320894976 }, { target := 634, numerator := 203326211286435444320894976 }, { target := 635, numerator := 203326211286435444320894976 }, { target := 636, numerator := 6506438761165934218268639232 }, { target := 637, numerator := 203326211286435444320894976 }, { target := 638, numerator := 234607166868963974216417280 }, { target := 639, numerator := 245034152063140150848258048 }, { target := 760, numerator := 180843024461493063458488320 }, { target := 761, numerator := 140655685692272382689935360 }, { target := 762, numerator := 160749355076882723074211840 }, { target := 763, numerator := 188880492215337199612198912 }, { target := 764, numerator := 2230397301691747782654689280 }, { target := 765, numerator := 5015379878398740959915409408 }, { target := 766, numerator := 140655685692272382689935360 }, { target := 767, numerator := 2230397301691747782654689280 }, { target := 768, numerator := 160749355076882723074211840 }, { target := 769, numerator := 156730621199960654997356544 }, { target := 770, numerator := 156730621199960654997356544 }, { target := 771, numerator := 156730621199960654997356544 }, { target := 772, numerator := 5015379878398740959915409408 }, { target := 773, numerator := 156730621199960654997356544 }, { target := 774, numerator := 180843024461493063458488320 }, { target := 775, numerator := 188880492215337199612198912 }, { target := 795, numerator := 171067725841952897866137600 }, { target := 796, numerator := 133052675654852253895884800 }, { target := 797, numerator := 152060200748402575881011200 }, { target := 798, numerator := 178670735879373026660188160 }, { target := 799, numerator := 2109835285384085740349030400 }, { target := 800, numerator := 4744278263350160367487549440 }, { target := 801, numerator := 133052675654852253895884800 }, { target := 802, numerator := 2109835285384085740349030400 }, { target := 803, numerator := 152060200748402575881011200 }, { target := 804, numerator := 148258695729692511483985920 }, { target := 805, numerator := 148258695729692511483985920 }, { target := 806, numerator := 148258695729692511483985920 }, { target := 807, numerator := 4744278263350160367487549440 }, { target := 808, numerator := 148258695729692511483985920 }, { target := 809, numerator := 171067725841952897866137600 }, { target := 810, numerator := 178670735879373026660188160 }]

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
    Slot5.Left15.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left7.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 120672774635964157130702848 }, { target := 72, numerator := 17822737309612396583340474368 }, { target := 74, numerator := 185763410331491458116139089920 }, { target := 82, numerator := 17822737309612396583340474368 }, { target := 89, numerator := 120672774635964157130702848 }, { target := 146, numerator := 12652322779129346954595663872 }, { target := 147, numerator := 1868681862409434063172274225152 }, { target := 149, numerator := 19476958536473469391284868218880 }, { target := 157, numerator := 1868681862409434063172274225152 }, { target := 164, numerator := 12652322779129346954595663872 }, { target := 200, numerator := 8292320998360507152104161280 }, { target := 202, numerator := 300516457748553835552188661760 }, { target := 205, numerator := 300516568187179199944353382400 }, { target := 212, numerator := 8292210559735142759939440640 }, { target := 242, numerator := 136379393577274416285351936000 }, { target := 243, numerator := 20142522731449593567249432576000 }, { target := 245, numerator := 209942145826029641884174909440000 }, { target := 253, numerator := 20142522731449593567249432576000 }, { target := 260, numerator := 136379393577274416285351936000 }, { target := 296, numerator := 694308863440960104738186067968 }, { target := 298, numerator := 25161983028147923042825410707456 }, { target := 301, numerator := 25161992275078483484635236925440 }, { target := 308, numerator := 694299616510399662928359849984 }, { target := 347, numerator := 70442053641244508585604415488 }, { target := 350, numerator := 238779537493599493588367966208 }, { target := 352, numerator := 70442053641244508585604415488 }, { target := 659, numerator := 694309114710724208384683278336 }, { target := 661, numerator := 25161992134247344745380904435712 }, { target := 664, numerator := 25162001381181251643188843642880 }, { target := 671, numerator := 694299867776817310576744071168 }, { target := 710, numerator := 682306879868878842017177665536 }, { target := 713, numerator := 2312836051508868199684952293376 }, { target := 715, numerator := 682306879868878842017177665536 }, { target := 746, numerator := 9903520314283042199192993792 }, { target := 748, numerator := 9903520314283042199192993792 }, { target := 891, numerator := 229719517559193891420241920 }, { target := 892, numerator := 178670735879373026660188160 }, { target := 893, numerator := 204195126719283459040215040 }, { target := 894, numerator := 239929273895158064372252672 }, { target := 895, numerator := 2833207383230057994182983680 }, { target := 896, numerator := 6370887953641643922054709248 }, { target := 897, numerator := 178670735879373026660188160 }, { target := 898, numerator := 2833207383230057994182983680 }, { target := 899, numerator := 204195126719283459040215040 }, { target := 900, numerator := 199090248551301372564209664 }, { target := 901, numerator := 199090248551301372564209664 }, { target := 902, numerator := 199090248551301372564209664 }, { target := 903, numerator := 6370887953641643922054709248 }, { target := 904, numerator := 199090248551301372564209664 }, { target := 905, numerator := 229719517559193891420241920 }, { target := 906, numerator := 239929273895158064372252672 }, { target := 1013, numerator := 9903520314283042199192993792 }, { target := 1015, numerator := 9903520314283042199192993792 }, { target := 1036, numerator := 8292069728596403505606950912 }, { target := 1038, numerator := 300507351649132132996694933504 }, { target := 1041, numerator := 300507462084411041390746664960 }, { target := 1048, numerator := 8291959293317495111555219456 }, { target := 1052, numerator := 70442053641244508585604415488 }, { target := 1055, numerator := 238779537493599493588367966208 }, { target := 1057, numerator := 70442053641244508585604415488 }, { target := 1088, numerator := 9903520314283042199192993792 }, { target := 1090, numerator := 9903520314283042199192993792 }, { target := 1102, numerator := 9903520314283042199192993792 }, { target := 1104, numerator := 9903520314283042199192993792 }]

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
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 553256823517405164391628800 }, { target := 6, numerator := 13242469775803697805760921600 }, { target := 7, numerator := 9905081840392253749592064000 }, { target := 8, numerator := 11493464333716416963490611200 }, { target := 9, numerator := 553256823517405164391628800 }, { target := 10, numerator := 11475617339409403893671526400 }, { target := 11, numerator := 11529158322330443103128780800 }, { target := 12, numerator := 553256823517405164391628800 }, { target := 13, numerator := 13242469775803697805760921600 }, { target := 14, numerator := 553256823517405164391628800 }, { target := 29, numerator := 2838814300618550019297902592 }, { target := 30, numerator := 238713742377643816242468880384 }, { target := 35, numerator := 238713684787026474661513789440 }, { target := 43, numerator := 2838871891235891600252993536 }, { target := 94, numerator := 1891622564312303238549340160 }, { target := 95, numerator := 45276901378055774290439045120 }, { target := 96, numerator := 33866145909462203141770444800 }, { target := 97, numerator := 39296933271520105987928227840 }, { target := 98, numerator := 1891622564312303238549340160 }, { target := 99, numerator := 39235913188800354270555668480 }, { target := 100, numerator := 39418973436959609422673346560 }, { target := 101, numerator := 1891622564312303238549340160 }, { target := 102, numerator := 45276901378055774290439045120 }, { target := 103, numerator := 1891622564312303238549340160 }, { target := 104, numerator := 99351422763955450322853298176 }, { target := 105, numerator := 8354385819938850244419704061952 }, { target := 110, numerator := 8354383804410828741255962296320 }, { target := 118, numerator := 99353438291976953486595063808 }, { target := 216, numerator := 553256644814571950330347520 }, { target := 217, numerator := 13242465498464915714358640640 }, { target := 218, numerator := 9905078641035078465591705600 }, { target := 219, numerator := 11493460621309172129443348480 }, { target := 220, numerator := 553256644814571950330347520 }, { target := 221, numerator := 11475613632766766582658498560 }, { target := 222, numerator := 11529154598393983223013048320 }, { target := 223, numerator := 553256644814571950330347520 }, { target := 224, numerator := 13242465498464915714358640640 }, { target := 225, numerator := 553256644814571950330347520 }, { target := 226, numerator := 99351471492063497141115420672 }, { target := 227, numerator := 8354389917448514157149939564544 }, { target := 232, numerator := 8354387901919504113867989975040 }, { target := 240, numerator := 99353487021073540423065010176 }, { target := 347, numerator := 553256823517405164391628800 }, { target := 350, numerator := 1891622564312303238549340160 }, { target := 352, numerator := 553256644814571950330347520 }, { target := 614, numerator := 13242469775803697805760921600 }, { target := 617, numerator := 45276901378055774290439045120 }, { target := 619, numerator := 13242465498464915714358640640 }, { target := 624, numerator := 2838789936564526610166841344 }, { target := 625, numerator := 238711693622811859877351129088 }, { target := 630, numerator := 238711636032688788355499950080 }, { target := 638, numerator := 2838847526687598132018020352 }, { target := 640, numerator := 12652332430634956485440831488 }, { target := 641, numerator := 1868683287886304383287173316608 }, { target := 643, numerator := 19476973393980494224641511915520 }, { target := 651, numerator := 1868683287886304383287173316608 }, { target := 658, numerator := 12652332430634956485440831488 }, { target := 1017, numerator := 120672774635964157130702848 }, { target := 1018, numerator := 17822737309612396583340474368 }, { target := 1020, numerator := 185763410331491458116139089920 }, { target := 1028, numerator := 17822737309612396583340474368 }, { target := 1035, numerator := 120672774635964157130702848 }]

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
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected,
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left6.expected,
    Slot13.Left14.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 120833500228180412001681408 }, { target := 72, numerator := 12669174567593823975046643712 }, { target := 74, numerator := 136561039013578724245241856000 }, { target := 82, numerator := 12669184231954395692267470848 }, { target := 89, numerator := 120833500228180412001681408 }, { target := 146, numerator := 17846475638474426946397667328 }, { target := 147, numerator := 1871170783376947960432759406592 }, { target := 149, numerator := 20169350811805813057882423296000 }, { target := 157, numerator := 1871172210752428922955909562368 }, { target := 164, numerator := 17846475638474426946397667328 }, { target := 200, numerator := 2819414658473092957662609408 }, { target := 202, numerator := 98672483656229103281922637824 }, { target := 205, numerator := 98672532051343245452223971328 }, { target := 212, numerator := 2819390460916021872511942656 }, { target := 242, numerator := 186010830963259560750816952320 }, { target := 243, numerator := 19502900143474632776196009492480 }, { target := 245, numerator := 210221770420896490101921546240000 }, { target := 253, numerator := 19502915020770558814711625809920 }, { target := 260, numerator := 186010830963259560750816952320 }, { target := 296, numerator := 237082441176885430254479343616 }, { target := 298, numerator := 8297294345087331905619569410048 }, { target := 301, numerator := 8297298414595790825779894419456 }, { target := 308, numerator := 237080406422655970174316838912 }, { target := 640, numerator := 17846475638474426946397667328 }, { target := 641, numerator := 1871170783376947960432759406592 }, { target := 643, numerator := 20169350811805813057882423296000 }, { target := 651, numerator := 1871172210752428922955909562368 }, { target := 658, numerator := 17846475638474426946397667328 }, { target := 659, numerator := 237082383979825838160410050560 }, { target := 661, numerator := 8297292343332850412728017223680 }, { target := 664, numerator := 8297296412840327548169575464960 }, { target := 671, numerator := 237080349226087270439630929920 }, { target := 710, numerator := 9905081840392253749592064000 }, { target := 713, numerator := 33866145909462203141770444800 }, { target := 715, numerator := 9905078641035078465591705600 }, { target := 736, numerator := 11493464333716416963490611200 }, { target := 739, numerator := 39296933271520105987928227840 }, { target := 741, numerator := 11493460621309172129443348480 }, { target := 881, numerator := 553256823517405164391628800 }, { target := 884, numerator := 1891622564312303238549340160 }, { target := 886, numerator := 553256644814571950330347520 }, { target := 977, numerator := 11475617339409403893671526400 }, { target := 980, numerator := 39235913188800354270555668480 }, { target := 982, numerator := 11475613632766766582658498560 }, { target := 1003, numerator := 11529158322330443103128780800 }, { target := 1006, numerator := 39418973436959609422673346560 }, { target := 1008, numerator := 11529154598393983223013048320 }, { target := 1036, numerator := 2819471855532685051731902464 }, { target := 1038, numerator := 98674485410710596173474824192 }, { target := 1041, numerator := 98674533806806523062542925824 }, { target := 1048, numerator := 2819447657484721607197851648 }, { target := 1052, numerator := 553256823517405164391628800 }, { target := 1055, numerator := 1891622564312303238549340160 }, { target := 1057, numerator := 553256644814571950330347520 }, { target := 1078, numerator := 13242469775803697805760921600 }, { target := 1081, numerator := 45276901378055774290439045120 }, { target := 1083, numerator := 13242465498464915714358640640 }, { target := 1092, numerator := 553256823517405164391628800 }, { target := 1095, numerator := 1891622564312303238549340160 }, { target := 1097, numerator := 553256644814571950330347520 }]

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
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot18.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 9903520314283042199192993792 }, { target := 2, numerator := 9903520314283042199192993792 }, { target := 3, numerator := 9903520314283042199192993792 }, { target := 4, numerator := 9903520314283042199192993792 }, { target := 5, numerator := 69184159826222285218004336640 }, { target := 7, numerator := 670122828442648862695442350080 }, { target := 12, numerator := 69184159826222285218004336640 }, { target := 29, numerator := 8304875610015859925990768640 }, { target := 30, numerator := 695360050213770036766555766784 }, { target := 35, numerator := 695360301863957704536666144768 }, { target := 43, numerator := 8304623959828192155880390656 }, { target := 90, numerator := 9903520314283042199192993792 }, { target := 91, numerator := 9903520314283042199192993792 }, { target := 92, numerator := 9903520314283042199192993792 }, { target := 93, numerator := 9903520314283042199192993792 }, { target := 94, numerator := 234515617181213788345718538240 }, { target := 96, numerator := 2271535407731924124690578145280 }, { target := 101, numerator := 234515617181213788345718538240 }, { target := 104, numerator := 300971441030534992002684026880 }, { target := 105, numerator := 25200078384738608770369431011328 }, { target := 110, numerator := 25200087504624706357410247213056 }, { target := 118, numerator := 300962321144437404961867825152 }, { target := 200, numerator := 234607166868963974216417280 }, { target := 201, numerator := 229719517559193891420241920 }, { target := 202, numerator := 180843024461493063458488320 }, { target := 203, numerator := 5684336147262606291951943680 }, { target := 204, numerator := 180843024461493063458488320 }, { target := 205, numerator := 180843024461493063458488320 }, { target := 206, numerator := 185730673771263146254663680 }, { target := 207, numerator := 185730673771263146254663680 }, { target := 208, numerator := 3142758506182163237940756480 }, { target := 209, numerator := 171067725841952897866137600 }, { target := 210, numerator := 5684336147262606291951943680 }, { target := 211, numerator := 3142758506182163237940756480 }, { target := 212, numerator := 234607166868963974216417280 }, { target := 213, numerator := 180843024461493063458488320 }, { target := 214, numerator := 171067725841952897866137600 }, { target := 215, numerator := 229719517559193891420241920 }, { target := 216, numerator := 69184159826222285218004336640 }, { target := 218, numerator := 670122828442648862695442350080 }, { target := 223, numerator := 69184159826222285218004336640 }, { target := 226, numerator := 300971551636364936810279731200 }, { target := 227, numerator := 25200087645669064080372761886720 }, { target := 232, numerator := 25200096765558513189961271869440 }, { target := 240, numerator := 300962431746915827221769748480 }, { target := 624, numerator := 8304765004185915118395064320 }, { target := 625, numerator := 695350789283314726763224891392 }, { target := 630, numerator := 695351040930150871985641488384 }, { target := 638, numerator := 8304513357349769895978467328 }, { target := 1017, numerator := 120833500228180412001681408 }, { target := 1018, numerator := 12669174567593823975046643712 }, { target := 1020, numerator := 136561039013578724245241856000 }, { target := 1028, numerator := 12669184231954395692267470848 }, { target := 1035, numerator := 120833500228180412001681408 }]

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
    Slot18.Left1.expected,
    Slot18.Left2.expected,
    Slot18.Left3.expected,
    Slot18.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 296, numerator := 182472240898083091057213440 }, { target := 297, numerator := 178670735879373026660188160 }, { target := 298, numerator := 140655685692272382689935360 }, { target := 299, numerator := 4421150336759804893740400640 }, { target := 300, numerator := 140655685692272382689935360 }, { target := 301, numerator := 140655685692272382689935360 }, { target := 302, numerator := 144457190710982447086960640 }, { target := 303, numerator := 144457190710982447086960640 }, { target := 304, numerator := 2444367727030571407287255040 }, { target := 305, numerator := 133052675654852253895884800 }, { target := 306, numerator := 4421150336759804893740400640 }, { target := 307, numerator := 2444367727030571407287255040 }, { target := 308, numerator := 182472240898083091057213440 }, { target := 309, numerator := 140655685692272382689935360 }, { target := 310, numerator := 133052675654852253895884800 }, { target := 311, numerator := 178670735879373026660188160 }, { target := 331, numerator := 208539703883523532636815360 }, { target := 332, numerator := 204195126719283459040215040 }, { target := 333, numerator := 160749355076882723074211840 }, { target := 334, numerator := 5052743242011205592846172160 }, { target := 335, numerator := 160749355076882723074211840 }, { target := 336, numerator := 160749355076882723074211840 }, { target := 337, numerator := 165093932241122796670812160 }, { target := 338, numerator := 165093932241122796670812160 }, { target := 339, numerator := 2793563116606367322614005760 }, { target := 340, numerator := 152060200748402575881011200 }, { target := 341, numerator := 5052743242011205592846172160 }, { target := 342, numerator := 2793563116606367322614005760 }, { target := 343, numerator := 208539703883523532636815360 }, { target := 344, numerator := 160749355076882723074211840 }, { target := 345, numerator := 152060200748402575881011200 }, { target := 346, numerator := 204195126719283459040215040 }, { target := 467, numerator := 245034152063140150848258048 }, { target := 468, numerator := 239929273895158064372252672 }, { target := 469, numerator := 188880492215337199612198912 }, { target := 470, numerator := 5936973309363166571594252288 }, { target := 471, numerator := 188880492215337199612198912 }, { target := 472, numerator := 188880492215337199612198912 }, { target := 473, numerator := 193985370383319286088204288 }, { target := 474, numerator := 193985370383319286088204288 }, { target := 475, numerator := 3282436662012481604071456768 }, { target := 476, numerator := 178670735879373026660188160 }, { target := 477, numerator := 5936973309363166571594252288 }, { target := 478, numerator := 3282436662012481604071456768 }, { target := 479, numerator := 245034152063140150848258048 }, { target := 480, numerator := 188880492215337199612198912 }, { target := 481, numerator := 178670735879373026660188160 }, { target := 482, numerator := 239929273895158064372252672 }, { target := 563, numerator := 2893488391383889015335813120 }, { target := 564, numerator := 2833207383230057994182983680 }, { target := 565, numerator := 2230397301691747782654689280 }, { target := 566, numerator := 70106812482905477600740638720 }, { target := 567, numerator := 2230397301691747782654689280 }, { target := 568, numerator := 2230397301691747782654689280 }, { target := 569, numerator := 2290678309845578803807518720 }, { target := 570, numerator := 2290678309845578803807518720 }, { target := 571, numerator := 38760688242913346601269329920 }, { target := 572, numerator := 2109835285384085740349030400 }, { target := 573, numerator := 70106812482905477600740638720 }, { target := 574, numerator := 38760688242913346601269329920 }, { target := 575, numerator := 2893488391383889015335813120 }, { target := 576, numerator := 2230397301691747782654689280 }, { target := 577, numerator := 2109835285384085740349030400 }, { target := 578, numerator := 2833207383230057994182983680 }]

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
    Slot18.Left5.expected,
    Slot18.Left6.expected,
    Slot18.Left7.expected,
    Slot18.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 598, numerator := 6506438761165934218268639232 }, { target := 599, numerator := 6370887953641643922054709248 }, { target := 600, numerator := 5015379878398740959915409408 }, { target := 601, numerator := 157645589150749614496800571392 }, { target := 602, numerator := 5015379878398740959915409408 }, { target := 603, numerator := 5015379878398740959915409408 }, { target := 604, numerator := 5150930685923031256129339392 }, { target := 605, numerator := 5150930685923031256129339392 }, { target := 606, numerator := 87159169238118660465556979712 }, { target := 607, numerator := 4744278263350160367487549440 }, { target := 608, numerator := 157645589150749614496800571392 }, { target := 609, numerator := 87159169238118660465556979712 }, { target := 610, numerator := 6506438761165934218268639232 }, { target := 611, numerator := 5015379878398740959915409408 }, { target := 612, numerator := 4744278263350160367487549440 }, { target := 613, numerator := 6370887953641643922054709248 }, { target := 659, numerator := 182472240898083091057213440 }, { target := 660, numerator := 178670735879373026660188160 }, { target := 661, numerator := 140655685692272382689935360 }, { target := 662, numerator := 4421150336759804893740400640 }, { target := 663, numerator := 140655685692272382689935360 }, { target := 664, numerator := 140655685692272382689935360 }, { target := 665, numerator := 144457190710982447086960640 }, { target := 666, numerator := 144457190710982447086960640 }, { target := 667, numerator := 2444367727030571407287255040 }, { target := 668, numerator := 133052675654852253895884800 }, { target := 669, numerator := 4421150336759804893740400640 }, { target := 670, numerator := 2444367727030571407287255040 }, { target := 671, numerator := 182472240898083091057213440 }, { target := 672, numerator := 140655685692272382689935360 }, { target := 673, numerator := 133052675654852253895884800 }, { target := 674, numerator := 178670735879373026660188160 }, { target := 694, numerator := 2893488391383889015335813120 }, { target := 695, numerator := 2833207383230057994182983680 }, { target := 696, numerator := 2230397301691747782654689280 }, { target := 697, numerator := 70106812482905477600740638720 }, { target := 698, numerator := 2230397301691747782654689280 }, { target := 699, numerator := 2230397301691747782654689280 }, { target := 700, numerator := 2290678309845578803807518720 }, { target := 701, numerator := 2290678309845578803807518720 }, { target := 702, numerator := 38760688242913346601269329920 }, { target := 703, numerator := 2109835285384085740349030400 }, { target := 704, numerator := 70106812482905477600740638720 }, { target := 705, numerator := 38760688242913346601269329920 }, { target := 706, numerator := 2893488391383889015335813120 }, { target := 707, numerator := 2230397301691747782654689280 }, { target := 708, numerator := 2109835285384085740349030400 }, { target := 709, numerator := 2833207383230057994182983680 }, { target := 720, numerator := 208539703883523532636815360 }, { target := 721, numerator := 204195126719283459040215040 }, { target := 722, numerator := 160749355076882723074211840 }, { target := 723, numerator := 5052743242011205592846172160 }, { target := 724, numerator := 160749355076882723074211840 }, { target := 725, numerator := 160749355076882723074211840 }, { target := 726, numerator := 165093932241122796670812160 }, { target := 727, numerator := 165093932241122796670812160 }, { target := 728, numerator := 2793563116606367322614005760 }, { target := 729, numerator := 152060200748402575881011200 }, { target := 730, numerator := 5052743242011205592846172160 }, { target := 731, numerator := 2793563116606367322614005760 }, { target := 732, numerator := 208539703883523532636815360 }, { target := 733, numerator := 160749355076882723074211840 }, { target := 734, numerator := 152060200748402575881011200 }, { target := 735, numerator := 204195126719283459040215040 }]

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
    Slot18.Left9.expected,
    Slot18.Left10.expected,
    Slot18.Left11.expected,
    Slot18.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 830, numerator := 203326211286435444320894976 }, { target := 831, numerator := 199090248551301372564209664 }, { target := 832, numerator := 156730621199960654997356544 }, { target := 833, numerator := 4926424660960925453025017856 }, { target := 834, numerator := 156730621199960654997356544 }, { target := 835, numerator := 156730621199960654997356544 }, { target := 836, numerator := 160966583935094726754041856 }, { target := 837, numerator := 160966583935094726754041856 }, { target := 838, numerator := 2723724038691208139548655616 }, { target := 839, numerator := 148258695729692511483985920 }, { target := 840, numerator := 4926424660960925453025017856 }, { target := 841, numerator := 2723724038691208139548655616 }, { target := 842, numerator := 203326211286435444320894976 }, { target := 843, numerator := 156730621199960654997356544 }, { target := 844, numerator := 148258695729692511483985920 }, { target := 845, numerator := 199090248551301372564209664 }, { target := 865, numerator := 203326211286435444320894976 }, { target := 866, numerator := 199090248551301372564209664 }, { target := 867, numerator := 156730621199960654997356544 }, { target := 868, numerator := 4926424660960925453025017856 }, { target := 869, numerator := 156730621199960654997356544 }, { target := 870, numerator := 156730621199960654997356544 }, { target := 871, numerator := 160966583935094726754041856 }, { target := 872, numerator := 160966583935094726754041856 }, { target := 873, numerator := 2723724038691208139548655616 }, { target := 874, numerator := 148258695729692511483985920 }, { target := 875, numerator := 4926424660960925453025017856 }, { target := 876, numerator := 2723724038691208139548655616 }, { target := 877, numerator := 203326211286435444320894976 }, { target := 878, numerator := 156730621199960654997356544 }, { target := 879, numerator := 148258695729692511483985920 }, { target := 880, numerator := 199090248551301372564209664 }, { target := 926, numerator := 203326211286435444320894976 }, { target := 927, numerator := 199090248551301372564209664 }, { target := 928, numerator := 156730621199960654997356544 }, { target := 929, numerator := 4926424660960925453025017856 }, { target := 930, numerator := 156730621199960654997356544 }, { target := 931, numerator := 156730621199960654997356544 }, { target := 932, numerator := 160966583935094726754041856 }, { target := 933, numerator := 160966583935094726754041856 }, { target := 934, numerator := 2723724038691208139548655616 }, { target := 935, numerator := 148258695729692511483985920 }, { target := 936, numerator := 4926424660960925453025017856 }, { target := 937, numerator := 2723724038691208139548655616 }, { target := 938, numerator := 203326211286435444320894976 }, { target := 939, numerator := 156730621199960654997356544 }, { target := 940, numerator := 148258695729692511483985920 }, { target := 941, numerator := 199090248551301372564209664 }, { target := 961, numerator := 6506438761165934218268639232 }, { target := 962, numerator := 6370887953641643922054709248 }, { target := 963, numerator := 5015379878398740959915409408 }, { target := 964, numerator := 157645589150749614496800571392 }, { target := 965, numerator := 5015379878398740959915409408 }, { target := 966, numerator := 5015379878398740959915409408 }, { target := 967, numerator := 5150930685923031256129339392 }, { target := 968, numerator := 5150930685923031256129339392 }, { target := 969, numerator := 87159169238118660465556979712 }, { target := 970, numerator := 4744278263350160367487549440 }, { target := 971, numerator := 157645589150749614496800571392 }, { target := 972, numerator := 87159169238118660465556979712 }, { target := 973, numerator := 6506438761165934218268639232 }, { target := 974, numerator := 5015379878398740959915409408 }, { target := 975, numerator := 4744278263350160367487549440 }, { target := 976, numerator := 6370887953641643922054709248 }]

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
    Slot18.Left13.expected,
    Slot18.Left14.expected,
    Slot18.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 987, numerator := 203326211286435444320894976 }, { target := 988, numerator := 199090248551301372564209664 }, { target := 989, numerator := 156730621199960654997356544 }, { target := 990, numerator := 4926424660960925453025017856 }, { target := 991, numerator := 156730621199960654997356544 }, { target := 992, numerator := 156730621199960654997356544 }, { target := 993, numerator := 160966583935094726754041856 }, { target := 994, numerator := 160966583935094726754041856 }, { target := 995, numerator := 2723724038691208139548655616 }, { target := 996, numerator := 148258695729692511483985920 }, { target := 997, numerator := 4926424660960925453025017856 }, { target := 998, numerator := 2723724038691208139548655616 }, { target := 999, numerator := 203326211286435444320894976 }, { target := 1000, numerator := 156730621199960654997356544 }, { target := 1001, numerator := 148258695729692511483985920 }, { target := 1002, numerator := 199090248551301372564209664 }, { target := 1036, numerator := 234607166868963974216417280 }, { target := 1037, numerator := 229719517559193891420241920 }, { target := 1038, numerator := 180843024461493063458488320 }, { target := 1039, numerator := 5684336147262606291951943680 }, { target := 1040, numerator := 180843024461493063458488320 }, { target := 1041, numerator := 180843024461493063458488320 }, { target := 1042, numerator := 185730673771263146254663680 }, { target := 1043, numerator := 185730673771263146254663680 }, { target := 1044, numerator := 3142758506182163237940756480 }, { target := 1045, numerator := 171067725841952897866137600 }, { target := 1046, numerator := 5684336147262606291951943680 }, { target := 1047, numerator := 3142758506182163237940756480 }, { target := 1048, numerator := 234607166868963974216417280 }, { target := 1049, numerator := 180843024461493063458488320 }, { target := 1050, numerator := 171067725841952897866137600 }, { target := 1051, numerator := 229719517559193891420241920 }, { target := 1062, numerator := 245034152063140150848258048 }, { target := 1063, numerator := 239929273895158064372252672 }, { target := 1064, numerator := 188880492215337199612198912 }, { target := 1065, numerator := 5936973309363166571594252288 }, { target := 1066, numerator := 188880492215337199612198912 }, { target := 1067, numerator := 188880492215337199612198912 }, { target := 1068, numerator := 193985370383319286088204288 }, { target := 1069, numerator := 193985370383319286088204288 }, { target := 1070, numerator := 3282436662012481604071456768 }, { target := 1071, numerator := 178670735879373026660188160 }, { target := 1072, numerator := 5936973309363166571594252288 }, { target := 1073, numerator := 3282436662012481604071456768 }, { target := 1074, numerator := 245034152063140150848258048 }, { target := 1075, numerator := 188880492215337199612198912 }, { target := 1076, numerator := 178670735879373026660188160 }, { target := 1077, numerator := 239929273895158064372252672 }]

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
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 35587006721770661093572608 }, { target := 72, numerator := 948986845913884295828602880 }, { target := 73, numerator := 907468671405151857886101504 }, { target := 74, numerator := 29655838934808884244643840 }, { target := 75, numerator := 931193342552998965281816576 }, { target := 76, numerator := 29655838934808884244643840 }, { target := 77, numerator := 907468671405151857886101504 }, { target := 78, numerator := 516011597465674585856802816 }, { target := 79, numerator := 931193342552998965281816576 }, { target := 80, numerator := 14537292245843315056724410368 }, { target := 81, numerator := 569392107548330577497161728 }, { target := 82, numerator := 948986845913884295828602880 }, { target := 83, numerator := 907468671405151857886101504 }, { target := 84, numerator := 29655838934808884244643840 }, { target := 85, numerator := 569392107548330577497161728 }, { target := 86, numerator := 29655838934808884244643840 }, { target := 87, numerator := 913399839192113634735030272 }, { target := 88, numerator := 516011597465674585856802816 }, { target := 89, numerator := 35587006721770661093572608 }, { target := 146, numerator := 5681365732628021100838649856 }, { target := 147, numerator := 151503086203413896022363996160 }, { target := 148, numerator := 144874826182014538071385571328 }, { target := 149, numerator := 4734471443856684250698874880 }, { target := 150, numerator := 148662403337099885471944671232 }, { target := 151, numerator := 4734471443856684250698874880 }, { target := 152, numerator := 144874826182014538071385571328 }, { target := 153, numerator := 82379803123106305962160422912 }, { target := 154, numerator := 148662403337099885471944671232 }, { target := 155, numerator := 2320837901778546619692588466176 }, { target := 156, numerator := 90901851722048337613418397696 }, { target := 157, numerator := 151503086203413896022363996160 }, { target := 158, numerator := 144874826182014538071385571328 }, { target := 159, numerator := 4734471443856684250698874880 }, { target := 160, numerator := 90901851722048337613418397696 }, { target := 161, numerator := 4734471443856684250698874880 }, { target := 162, numerator := 145821720470785874921525346304 }, { target := 163, numerator := 82379803123106305962160422912 }, { target := 164, numerator := 5681365732628021100838649856 }, { target := 242, numerator := 56691486368813538954493034496 }, { target := 243, numerator := 1511772969835027705453147586560 }, { target := 244, numerator := 1445632902404745243339572379648 }, { target := 245, numerator := 47242905307344615795410862080 }, { target := 246, numerator := 1483427226650620935975901069312 }, { target := 247, numerator := 47242905307344615795410862080 }, { target := 248, numerator := 1445632902404745243339572379648 }, { target := 249, numerator := 822026552347796314840149000192 }, { target := 250, numerator := 1483427226650620935975901069312 }, { target := 251, numerator := 23158472181660330662910404591616 }, { target := 252, numerator := 907063781901016623271888551936 }, { target := 253, numerator := 1511772969835027705453147586560 }, { target := 254, numerator := 1445632902404745243339572379648 }, { target := 255, numerator := 47242905307344615795410862080 }, { target := 256, numerator := 907063781901016623271888551936 }, { target := 257, numerator := 47242905307344615795410862080 }, { target := 258, numerator := 1455081483466214166498654552064 }, { target := 259, numerator := 822026552347796314840149000192 }, { target := 260, numerator := 56691486368813538954493034496 }]

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
    Slot19.Left11.expected,
    Slot19.Left18.expected,
    Slot20.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 7906857496279933320859484160 }, { target := 30, numerator := 8132767710459359987169755136 }, { target := 31, numerator := 7906857496279933320859484160 }, { target := 32, numerator := 7003216639562226655618400256 }, { target := 33, numerator := 327795720774348092816203186176 }, { target := 34, numerator := 89234534600873533192557035520 }, { target := 35, numerator := 8132767710459359987169755136 }, { target := 36, numerator := 327795720774348092816203186176 }, { target := 37, numerator := 7906857496279933320859484160 }, { target := 38, numerator := 7906857496279933320859484160 }, { target := 39, numerator := 6777306425382799989308129280 }, { target := 40, numerator := 7906857496279933320859484160 }, { target := 41, numerator := 89234534600873533192557035520 }, { target := 42, numerator := 6777306425382799989308129280 }, { target := 43, numerator := 7906857496279933320859484160 }, { target := 44, numerator := 7003216639562226655618400256 }, { target := 640, numerator := 5681365732628021100838649856 }, { target := 641, numerator := 151503086203413896022363996160 }, { target := 642, numerator := 144874826182014538071385571328 }, { target := 643, numerator := 4734471443856684250698874880 }, { target := 644, numerator := 148662403337099885471944671232 }, { target := 645, numerator := 4734471443856684250698874880 }, { target := 646, numerator := 144874826182014538071385571328 }, { target := 647, numerator := 82379803123106305962160422912 }, { target := 648, numerator := 148662403337099885471944671232 }, { target := 649, numerator := 2320837901778546619692588466176 }, { target := 650, numerator := 90901851722048337613418397696 }, { target := 651, numerator := 151503086203413896022363996160 }, { target := 652, numerator := 144874826182014538071385571328 }, { target := 653, numerator := 4734471443856684250698874880 }, { target := 654, numerator := 90901851722048337613418397696 }, { target := 655, numerator := 4734471443856684250698874880 }, { target := 656, numerator := 145821720470785874921525346304 }, { target := 657, numerator := 82379803123106305962160422912 }, { target := 658, numerator := 5681365732628021100838649856 }, { target := 1017, numerator := 35582946132231435778523136 }, { target := 1018, numerator := 948878563526171620760616960 }, { target := 1019, numerator := 907365126371901612352339968 }, { target := 1020, numerator := 29652455110192863148769280 }, { target := 1021, numerator := 931087090460055902871355392 }, { target := 1022, numerator := 29652455110192863148769280 }, { target := 1023, numerator := 907365126371901612352339968 }, { target := 1024, numerator := 515952718917355818788585472 }, { target := 1025, numerator := 931087090460055902871355392 }, { target := 1026, numerator := 14535633495016541515526701056 }, { target := 1027, numerator := 569327138115702972456370176 }, { target := 1028, numerator := 948878563526171620760616960 }, { target := 1029, numerator := 907365126371901612352339968 }, { target := 1030, numerator := 29652455110192863148769280 }, { target := 1031, numerator := 569327138115702972456370176 }, { target := 1032, numerator := 29652455110192863148769280 }, { target := 1033, numerator := 913295617393940184982093824 }, { target := 1034, numerator := 515952718917355818788585472 }, { target := 1035, numerator := 35582946132231435778523136 }]

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
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 7476755909293642195402752000 }, { target := 6, numerator := 149834188422244589595871150080 }, { target := 7, numerator := 251518068788638123453348577280 }, { target := 8, numerator := 241349680751998770067600834560 }, { target := 9, numerator := 7476755909293642195402752000 }, { target := 10, numerator := 241349680751998770067600834560 }, { target := 11, numerator := 161198857404370925732883333120 }, { target := 12, numerator := 7775826145665387883218862080 }, { target := 13, numerator := 149834188422244589595871150080 }, { target := 14, numerator := 7177685672921896507586641920 }, { target := 104, numerator := 297080948276098714874014597120 }, { target := 105, numerator := 305568975369701535298986442752 }, { target := 106, numerator := 297080948276098714874014597120 }, { target := 107, numerator := 263128839901687433174127214592 }, { target := 108, numerator := 12316127312817692436634148012032 }, { target := 109, numerator := 3352770701973114067863879024640 }, { target := 110, numerator := 305568975369701535298986442752 }, { target := 111, numerator := 12316127312817692436634148012032 }, { target := 112, numerator := 297080948276098714874014597120 }, { target := 113, numerator := 297080948276098714874014597120 }, { target := 114, numerator := 254640812808084612749155368960 }, { target := 115, numerator := 297080948276098714874014597120 }, { target := 116, numerator := 3352770701973114067863879024640 }, { target := 117, numerator := 254640812808084612749155368960 }, { target := 118, numerator := 297080948276098714874014597120 }, { target := 119, numerator := 263128839901687433174127214592 }, { target := 226, numerator := 297058479415476388737832714240 }, { target := 227, numerator := 305545864541632856987485077504 }, { target := 228, numerator := 297058479415476388737832714240 }, { target := 229, numerator := 263108938910850515739223261184 }, { target := 230, numerator := 12315195818053035430245579096064 }, { target := 231, numerator := 3352517124831804958612683489280 }, { target := 232, numerator := 305545864541632856987485077504 }, { target := 233, numerator := 12315195818053035430245579096064 }, { target := 234, numerator := 297058479415476388737832714240 }, { target := 235, numerator := 297058479415476388737832714240 }, { target := 236, numerator := 254621553784694047489570897920 }, { target := 237, numerator := 297058479415476388737832714240 }, { target := 238, numerator := 3352517124831804958612683489280 }, { target := 239, numerator := 254621553784694047489570897920 }, { target := 240, numerator := 297058479415476388737832714240 }, { target := 241, numerator := 263108938910850515739223261184 }, { target := 624, numerator := 7929326356902259457041367040 }, { target := 625, numerator := 8155878538528038298671120384 }, { target := 626, numerator := 7929326356902259457041367040 }, { target := 627, numerator := 7023117630399144090522353664 }, { target := 628, numerator := 328727215539005099204772102144 }, { target := 629, numerator := 89488111742182642443752570880 }, { target := 630, numerator := 8155878538528038298671120384 }, { target := 631, numerator := 328727215539005099204772102144 }, { target := 632, numerator := 7929326356902259457041367040 }, { target := 633, numerator := 7929326356902259457041367040 }, { target := 634, numerator := 6796565448773365248892600320 }, { target := 635, numerator := 7929326356902259457041367040 }, { target := 636, numerator := 89488111742182642443752570880 }, { target := 637, numerator := 6796565448773365248892600320 }, { target := 638, numerator := 7929326356902259457041367040 }, { target := 639, numerator := 7023117630399144090522353664 }]

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
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 51742025079506128677424332800 }, { target := 2, numerator := 47293178063324293314505605120 }, { target := 3, numerator := 51742025079506128677424332800 }, { target := 4, numerator := 47293178063324293314505605120 }, { target := 90, numerator := 51742025079506128677424332800 }, { target := 91, numerator := 47293178063324293314505605120 }, { target := 92, numerator := 51742025079506128677424332800 }, { target := 93, numerator := 47293178063324293314505605120 }, { target := 94, numerator := 25666395720464255879322009600 }, { target := 95, numerator := 514354570238103687821613072384 }, { target := 96, numerator := 863417552036417567780392402944 }, { target := 97, numerator := 828511253856586179784514469888 }, { target := 98, numerator := 25666395720464255879322009600 }, { target := 99, numerator := 828511253856586179784514469888 }, { target := 100, numerator := 553367491733209356758182526976 }, { target := 101, numerator := 26693051549282826114494889984 }, { target := 102, numerator := 514354570238103687821613072384 }, { target := 103, numerator := 24639739891645685644149129216 }, { target := 216, numerator := 7476755909293642195402752000 }, { target := 217, numerator := 149834188422244589595871150080 }, { target := 218, numerator := 251518068788638123453348577280 }, { target := 219, numerator := 241349680751998770067600834560 }, { target := 220, numerator := 7476755909293642195402752000 }, { target := 221, numerator := 241349680751998770067600834560 }, { target := 222, numerator := 161198857404370925732883333120 }, { target := 223, numerator := 7775826145665387883218862080 }, { target := 224, numerator := 149834188422244589595871150080 }, { target := 225, numerator := 7177685672921896507586641920 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent1
