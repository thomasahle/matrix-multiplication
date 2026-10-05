import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk14Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 61; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left7.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 219158387642113698929049600 }, { target := 201, numerator := 260250585325010017478246400 }, { target := 202, numerator := 198612288800665539654451200 }, { target := 203, numerator := 2047761184530999874368307200 }, { target := 204, numerator := 246553186097377911295180800 }, { target := 205, numerator := 198612288800665539654451200 }, { target := 206, numerator := 246553186097377911295180800 }, { target := 207, numerator := 246553186097377911295180800 }, { target := 208, numerator := 10560694804504353867143577600 }, { target := 209, numerator := 246553186097377911295180800 }, { target := 210, numerator := 2047761184530999874368307200 }, { target := 211, numerator := 10560694804504353867143577600 }, { target := 212, numerator := 219158387642113698929049600 }, { target := 213, numerator := 246553186097377911295180800 }, { target := 214, numerator := 246553186097377911295180800 }, { target := 215, numerator := 260250585325010017478246400 }, { target := 296, numerator := 18349942201638590424557813760 }, { target := 297, numerator := 21790556364445826129162403840 }, { target := 298, numerator := 16629635120234972572255518720 }, { target := 299, numerator := 171457272446560579279462072320 }, { target := 300, numerator := 20643684976843414227627540480 }, { target := 301, numerator := 16629635120234972572255518720 }, { target := 302, numerator := 20643684976843414227627540480 }, { target := 303, numerator := 20643684976843414227627540480 }, { target := 304, numerator := 884237839841459576083379650560 }, { target := 305, numerator := 20643684976843414227627540480 }, { target := 306, numerator := 171457272446560579279462072320 }, { target := 307, numerator := 884237839841459576083379650560 }, { target := 308, numerator := 18349942201638590424557813760 }, { target := 309, numerator := 20643684976843414227627540480 }, { target := 310, numerator := 20643684976843414227627540480 }, { target := 311, numerator := 21790556364445826129162403840 }, { target := 347, numerator := 10940044363627291531970347008 }, { target := 350, numerator := 39137286391535537041698717696 }, { target := 352, numerator := 10940040726708539226977206272 }, { target := 710, numerator := 105966069265804780982004350976 }, { target := 713, numerator := 379086616360487581993414950912 }, { target := 715, numerator := 105966034038343939765183709184 }, { target := 746, numerator := 9903520314283042199192993792 }, { target := 748, numerator := 9903520314283042199192993792 }, { target := 1013, numerator := 9903520314283042199192993792 }, { target := 1015, numerator := 9903520314283042199192993792 }, { target := 1052, numerator := 10940044363627291531970347008 }, { target := 1055, numerator := 39137286391535537041698717696 }, { target := 1057, numerator := 10940040726708539226977206272 }, { target := 1088, numerator := 9903520314283042199192993792 }, { target := 1090, numerator := 9903520314283042199192993792 }, { target := 1102, numerator := 9903520314283042199192993792 }, { target := 1104, numerator := 9903520314283042199192993792 }]

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
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 347, numerator := 4467514574699636245508653056 }, { target := 350, numerator := 16249313524812682476461752320 }, { target := 352, numerator := 4467514574699636245508653056 }, { target := 614, numerator := 106932123046036454650561953792 }, { target := 617, numerator := 388935181787451948307568394240 }, { target := 619, numerator := 106932123046036454650561953792 }, { target := 659, numerator := 18349948842466456959996395520 }, { target := 660, numerator := 21790564250428917639995719680 }, { target := 661, numerator := 16629641138485226619996733440 }, { target := 662, numerator := 171457334496795957219966320640 }, { target := 663, numerator := 20643692447774764079995944960 }, { target := 664, numerator := 16629641138485226619996733440 }, { target := 665, numerator := 20643692447774764079995944960 }, { target := 666, numerator := 20643692447774764079995944960 }, { target := 667, numerator := 884238159846352394759826309120 }, { target := 668, numerator := 20643692447774764079995944960 }, { target := 669, numerator := 171457334496795957219966320640 }, { target := 670, numerator := 884238159846352394759826309120 }, { target := 671, numerator := 18349948842466456959996395520 }, { target := 672, numerator := 20643692447774764079995944960 }, { target := 673, numerator := 20643692447774764079995944960 }, { target := 674, numerator := 21790564250428917639995719680 }, { target := 710, numerator := 79982922224461229556687175680 }, { target := 713, numerator := 290915129234549637885041049600 }, { target := 715, numerator := 79982922224461229556687175680 }, { target := 736, numerator := 92809012455050507809921695744 }, { target := 739, numerator := 337566384192882823059398983680 }, { target := 741, numerator := 92809012455050507809921695744 }, { target := 881, numerator := 4467514574699636245508653056 }, { target := 884, numerator := 16249313524812682476461752320 }, { target := 886, numerator := 4467514574699636245508653056 }, { target := 977, numerator := 92664899081673100189098835968 }, { target := 980, numerator := 337042212788856607495642152960 }, { target := 982, numerator := 92664899081673100189098835968 }, { target := 1003, numerator := 93097239201805323051567415296 }, { target := 1006, numerator := 338614727000935254186912645120 }, { target := 1008, numerator := 93097239201805323051567415296 }, { target := 1036, numerator := 219151746814247163490467840 }, { target := 1037, numerator := 260242699341918506644930560 }, { target := 1038, numerator := 198606270550411491913236480 }, { target := 1039, numerator := 2047699134295621933864058880 }, { target := 1040, numerator := 246545715166028058926776320 }, { target := 1041, numerator := 198606270550411491913236480 }, { target := 1042, numerator := 246545715166028058926776320 }, { target := 1043, numerator := 246545715166028058926776320 }, { target := 1044, numerator := 10560374799611535190696919040 }, { target := 1045, numerator := 246545715166028058926776320 }, { target := 1046, numerator := 2047699134295621933864058880 }, { target := 1047, numerator := 10560374799611535190696919040 }, { target := 1048, numerator := 219151746814247163490467840 }, { target := 1049, numerator := 246545715166028058926776320 }, { target := 1050, numerator := 246545715166028058926776320 }, { target := 1051, numerator := 260242699341918506644930560 }, { target := 1052, numerator := 4467514574699636245508653056 }, { target := 1055, numerator := 16249313524812682476461752320 }, { target := 1057, numerator := 4467514574699636245508653056 }, { target := 1078, numerator := 106932123046036454650561953792 }, { target := 1081, numerator := 388935181787451948307568394240 }, { target := 1083, numerator := 106932123046036454650561953792 }, { target := 1092, numerator := 4467514574699636245508653056 }, { target := 1095, numerator := 16249313524812682476461752320 }, { target := 1097, numerator := 4467514574699636245508653056 }]

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
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 53022502591202464303677440 }, { target := 72, numerator := 890778043532201400301780992 }, { target := 73, numerator := 1930019094319769700653858816 }, { target := 74, numerator := 63627003109442957164412928 }, { target := 75, numerator := 1018032049751087314630606848 }, { target := 76, numerator := 74231503627683450025148416 }, { target := 77, numerator := 1930019094319769700653858816 }, { target := 78, numerator := 1930019094319769700653858816 }, { target := 79, numerator := 1018032049751087314630606848 }, { target := 80, numerator := 23817708163968146965211906048 }, { target := 81, numerator := 1908810093283288714932387840 }, { target := 82, numerator := 890778043532201400301780992 }, { target := 83, numerator := 1930019094319769700653858816 }, { target := 84, numerator := 74231503627683450025148416 }, { target := 85, numerator := 1908810093283288714932387840 }, { target := 86, numerator := 74231503627683450025148416 }, { target := 87, numerator := 1930019094319769700653858816 }, { target := 88, numerator := 1930019094319769700653858816 }, { target := 89, numerator := 63627003109442957164412928 }, { target := 146, numerator := 7831146155643325733970903040 }, { target := 147, numerator := 131563255414807872330711171072 }, { target := 148, numerator := 285053720065417056716540870656 }, { target := 149, numerator := 9397375386771990880765083648 }, { target := 150, numerator := 150358006188351854092241338368 }, { target := 151, numerator := 10963604617900656027559264256 }, { target := 152, numerator := 285053720065417056716540870656 }, { target := 153, numerator := 285053720065417056716540870656 }, { target := 154, numerator := 150358006188351854092241338368 }, { target := 155, numerator := 3517750853114981919699729645568 }, { target := 156, numerator := 281921261603159726422952509440 }, { target := 157, numerator := 131563255414807872330711171072 }, { target := 158, numerator := 285053720065417056716540870656 }, { target := 159, numerator := 10963604617900656027559264256 }, { target := 160, numerator := 281921261603159726422952509440 }, { target := 161, numerator := 10963604617900656027559264256 }, { target := 162, numerator := 285053720065417056716540870656 }, { target := 163, numerator := 285053720065417056716540870656 }, { target := 164, numerator := 9397375386771990880765083648 }, { target := 200, numerator := 3756027391062189780768915456 }, { target := 202, numerator := 138705094565474984188685844480 }, { target := 205, numerator := 138705060600096710096685367296 }, { target := 212, numerator := 3756061356440463872769392640 }, { target := 296, numerator := 315841495795631800161782464512 }, { target := 298, numerator := 11663606246930274677680987176960 }, { target := 301, numerator := 11663603390807365435550116872192 }, { target := 308, numerator := 315844351918541042292652769280 }, { target := 659, numerator := 315841419597644437611526225920 }, { target := 661, numerator := 11663603433039974524008372633600 }, { target := 664, numerator := 11663600576917754332620490014720 }, { target := 671, numerator := 315844275719864628999408844800 }, { target := 1036, numerator := 3756103589049552331025154048 }, { target := 1038, numerator := 138707908455775137861300387840 }, { target := 1041, numerator := 138707874489707813026312224768 }, { target := 1048, numerator := 3756137555116877166013317120 }]

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
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 6476427116819745605765038080 }, { target := 202, numerator := 243336004248347227055519170560 }, { target := 205, numerator := 243317600231544478233652101120 }, { target := 212, numerator := 6494831133622494427632107520 }, { target := 242, numerator := 81622726711685469917780377600 }, { target := 243, numerator := 1371261808756315894618710343680 }, { target := 244, numerator := 2971067252305351105007205744640 }, { target := 245, numerator := 97947272054022563901336453120 }, { target := 246, numerator := 1567156352864361022421383249920 }, { target := 247, numerator := 114271817396359657884892528640 }, { target := 248, numerator := 2971067252305351105007205744640 }, { target := 249, numerator := 2971067252305351105007205744640 }, { target := 250, numerator := 1567156352864361022421383249920 }, { target := 251, numerator := 36664928838889113087066945617920 }, { target := 252, numerator := 2938418161620676917040093593600 }, { target := 253, numerator := 1371261808756315894618710343680 }, { target := 254, numerator := 2971067252305351105007205744640 }, { target := 255, numerator := 114271817396359657884892528640 }, { target := 256, numerator := 2938418161620676917040093593600 }, { target := 257, numerator := 114271817396359657884892528640 }, { target := 258, numerator := 2971067252305351105007205744640 }, { target := 259, numerator := 2971067252305351105007205744640 }, { target := 260, numerator := 97947272054022563901336453120 }, { target := 640, numerator := 7831146155643325733970903040 }, { target := 641, numerator := 131563255414807872330711171072 }, { target := 642, numerator := 285053720065417056716540870656 }, { target := 643, numerator := 9397375386771990880765083648 }, { target := 644, numerator := 150358006188351854092241338368 }, { target := 645, numerator := 10963604617900656027559264256 }, { target := 646, numerator := 285053720065417056716540870656 }, { target := 647, numerator := 285053720065417056716540870656 }, { target := 648, numerator := 150358006188351854092241338368 }, { target := 649, numerator := 3517750853114981919699729645568 }, { target := 650, numerator := 281921261603159726422952509440 }, { target := 651, numerator := 131563255414807872330711171072 }, { target := 652, numerator := 285053720065417056716540870656 }, { target := 653, numerator := 10963604617900656027559264256 }, { target := 654, numerator := 281921261603159726422952509440 }, { target := 655, numerator := 10963604617900656027559264256 }, { target := 656, numerator := 285053720065417056716540870656 }, { target := 657, numerator := 285053720065417056716540870656 }, { target := 658, numerator := 9397375386771990880765083648 }, { target := 1017, numerator := 53022502591202464303677440 }, { target := 1018, numerator := 890778043532201400301780992 }, { target := 1019, numerator := 1930019094319769700653858816 }, { target := 1020, numerator := 63627003109442957164412928 }, { target := 1021, numerator := 1018032049751087314630606848 }, { target := 1022, numerator := 74231503627683450025148416 }, { target := 1023, numerator := 1930019094319769700653858816 }, { target := 1024, numerator := 1930019094319769700653858816 }, { target := 1025, numerator := 1018032049751087314630606848 }, { target := 1026, numerator := 23817708163968146965211906048 }, { target := 1027, numerator := 1908810093283288714932387840 }, { target := 1028, numerator := 890778043532201400301780992 }, { target := 1029, numerator := 1930019094319769700653858816 }, { target := 1030, numerator := 74231503627683450025148416 }, { target := 1031, numerator := 1908810093283288714932387840 }, { target := 1032, numerator := 74231503627683450025148416 }, { target := 1033, numerator := 1930019094319769700653858816 }, { target := 1034, numerator := 1930019094319769700653858816 }, { target := 1035, numerator := 63627003109442957164412928 }]

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
    Slot9.Left11.expected,
    Slot9.Left12.expected,
    Slot9.Left13.expected,
    Slot9.Left14.expected,
    Slot9.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 296, numerator := 5037221090859802137817251840 }, { target := 298, numerator := 189261336637603398820959354880 }, { target := 301, numerator := 189247022402312371959507189760 }, { target := 308, numerator := 5051535326150828999269416960 }, { target := 331, numerator := 5756824103839773871791144960 }, { target := 333, numerator := 216298670442975312938239262720 }, { target := 336, numerator := 216282311316928425096579645440 }, { target := 343, numerator := 5773183229886661713450762240 }, { target := 467, numerator := 6764268322011734299354595328 }, { target := 469, numerator := 254150937770495992702431133696 }, { target := 472, numerator := 254131715797390899488481083392 }, { target := 479, numerator := 6783490295116827513304645632 }, { target := 563, numerator := 79875934440776862471102136320 }, { target := 565, numerator := 3001144052396282467018069770240 }, { target := 568, numerator := 3000917069522381898215042580480 }, { target := 575, numerator := 80102917314677431274129326080 }, { target := 598, numerator := 179612912039800944799883722752 }, { target := 600, numerator := 6748518517820829763673064996864 }, { target := 603, numerator := 6748008113088166863013284937728 }, { target := 610, numerator := 180123316772463845459663781888 }, { target := 659, numerator := 5037221090859802137817251840 }, { target := 661, numerator := 189261336637603398820959354880 }, { target := 664, numerator := 189247022402312371959507189760 }, { target := 671, numerator := 5051535326150828999269416960 }, { target := 694, numerator := 79875934440776862471102136320 }, { target := 696, numerator := 3001144052396282467018069770240 }, { target := 699, numerator := 3000917069522381898215042580480 }, { target := 706, numerator := 80102917314677431274129326080 }, { target := 720, numerator := 5756824103839773871791144960 }, { target := 722, numerator := 216298670442975312938239262720 }, { target := 725, numerator := 216282311316928425096579645440 }, { target := 732, numerator := 5773183229886661713450762240 }, { target := 830, numerator := 5612903501243779524996366336 }, { target := 832, numerator := 210891203681900930114783281152 }, { target := 835, numerator := 210875253534005214469165154304 }, { target := 842, numerator := 5628853649139495170614493184 }, { target := 865, numerator := 5612903501243779524996366336 }, { target := 867, numerator := 210891203681900930114783281152 }, { target := 870, numerator := 210875253534005214469165154304 }, { target := 877, numerator := 5628853649139495170614493184 }, { target := 926, numerator := 5612903501243779524996366336 }, { target := 928, numerator := 210891203681900930114783281152 }, { target := 931, numerator := 210875253534005214469165154304 }, { target := 938, numerator := 5628853649139495170614493184 }, { target := 961, numerator := 179612912039800944799883722752 }, { target := 963, numerator := 6748518517820829763673064996864 }, { target := 966, numerator := 6748008113088166863013284937728 }, { target := 973, numerator := 180123316772463845459663781888 }, { target := 987, numerator := 5612903501243779524996366336 }, { target := 989, numerator := 210891203681900930114783281152 }, { target := 992, numerator := 210875253534005214469165154304 }, { target := 999, numerator := 5628853649139495170614493184 }, { target := 1036, numerator := 6476427116819745605765038080 }, { target := 1038, numerator := 243336004248347227055519170560 }, { target := 1041, numerator := 243317600231544478233652101120 }, { target := 1048, numerator := 6494831133622494427632107520 }, { target := 1062, numerator := 6764268322011734299354595328 }, { target := 1064, numerator := 254150937770495992702431133696 }, { target := 1067, numerator := 254131715797390899488481083392 }, { target := 1074, numerator := 6783490295116827513304645632 }]

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
  [{ target := 29, numerator := 6498993064961974684530769920 }, { target := 30, numerator := 5054772383859313643523932160 }, { target := 31, numerator := 5776882724410644164027351040 }, { target := 32, numerator := 6787837201182506892732137472 }, { target := 33, numerator := 80154247801197687775879495680 }, { target := 34, numerator := 180238741001612097917653352448 }, { target := 35, numerator := 5054772383859313643523932160 }, { target := 36, numerator := 80154247801197687775879495680 }, { target := 37, numerator := 5776882724410644164027351040 }, { target := 38, numerator := 5632460656300378059926667264 }, { target := 39, numerator := 5632460656300378059926667264 }, { target := 40, numerator := 5632460656300378059926667264 }, { target := 41, numerator := 180238741001612097917653352448 }, { target := 42, numerator := 5632460656300378059926667264 }, { target := 43, numerator := 6498993064961974684530769920 }, { target := 44, numerator := 6787837201182506892732137472 }, { target := 71, numerator := 49984155551751625571827712 }, { target := 72, numerator := 7979830131437948815104016384 }, { target := 74, numerator := 79626704636140607370736697344 }, { target := 82, numerator := 7979830131437948815104016384 }, { target := 89, numerator := 49978452202190722830434304 }, { target := 104, numerator := 244183864890327530982541885440 }, { target := 105, numerator := 189920783803588079653088133120 }, { target := 106, numerator := 217052324346957805317815009280 }, { target := 107, numerator := 255036481107675421248432635904 }, { target := 108, numerator := 3011601000314039548784683253760 }, { target := 109, numerator := 6772032519625083525915828289536 }, { target := 110, numerator := 189920783803588079653088133120 }, { target := 111, numerator := 3011601000314039548784683253760 }, { target := 112, numerator := 217052324346957805317815009280 }, { target := 113, numerator := 211626016238283860184869634048 }, { target := 114, numerator := 211626016238283860184869634048 }, { target := 115, numerator := 211626016238283860184869634048 }, { target := 116, numerator := 6772032519625083525915828289536 }, { target := 117, numerator := 211626016238283860184869634048 }, { target := 118, numerator := 244183864890327530982541885440 }, { target := 119, numerator := 255036481107675421248432635904 }, { target := 146, numerator := 7979830131437948815104016384 }, { target := 147, numerator := 1273957481599856596161017151488 }, { target := 149, numerator := 12712179887978874774252796510208 }, { target := 157, numerator := 1273957481599856596161017151488 }, { target := 164, numerator := 7978919607689496287854460928 }, { target := 242, numerator := 79626704636140607370736697344 }, { target := 243, numerator := 12712179887978874774252796510208 }, { target := 245, numerator := 126848438694669217567497915465728 }, { target := 253, numerator := 12712179887978874774252796510208 }, { target := 260, numerator := 79617618978377469464829493248 }, { target := 640, numerator := 7979830131437948815104016384 }, { target := 641, numerator := 1273957481599856596161017151488 }, { target := 643, numerator := 12712179887978874774252796510208 }, { target := 651, numerator := 1273957481599856596161017151488 }, { target := 658, numerator := 7978919607689496287854460928 }, { target := 1017, numerator := 49978452202190722830434304 }, { target := 1018, numerator := 7978919607689496287854460928 }, { target := 1020, numerator := 79617618978377469464829493248 }, { target := 1028, numerator := 7978919607689496287854460928 }, { target := 1035, numerator := 49972749503399966244077568 }]

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
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 52811886890740885498101760 }, { target := 72, numerator := 7800039318878108948533084160 }, { target := 74, numerator := 81298505354340145310361190400 }, { target := 82, numerator := 7800039318878108948533084160 }, { target := 89, numerator := 52811886890740885498101760 }, { target := 146, numerator := 887239699764446876368109568 }, { target := 147, numerator := 131040660557152230335355813888 }, { target := 149, numerator := 1365814889952914441214067998720 }, { target := 157, numerator := 131040660557152230335355813888 }, { target := 164, numerator := 887239699764446876368109568 }, { target := 181, numerator := 1922352682822968232130904064 }, { target := 182, numerator := 283921431207163165726604263424 }, { target := 184, numerator := 2959265594897981289297147330560 }, { target := 192, numerator := 283921431207163165726604263424 }, { target := 199, numerator := 1922352682822968232130904064 }, { target := 226, numerator := 244165396748030695927846010880 }, { target := 227, numerator := 189906419692912763499435786240 }, { target := 228, numerator := 217035908220471729713640898560 }, { target := 229, numerator := 255017192159054282413528055808 }, { target := 230, numerator := 3011373226559045249776767467520 }, { target := 231, numerator := 6771520336478717967065596035072 }, { target := 232, numerator := 189906419692912763499435786240 }, { target := 233, numerator := 3011373226559045249776767467520 }, { target := 234, numerator := 217035908220471729713640898560 }, { target := 235, numerator := 211610010514959936470799876096 }, { target := 236, numerator := 211610010514959936470799876096 }, { target := 237, numerator := 211610010514959936470799876096 }, { target := 238, numerator := 6771520336478717967065596035072 }, { target := 239, numerator := 211610010514959936470799876096 }, { target := 240, numerator := 244165396748030695927846010880 }, { target := 241, numerator := 255017192159054282413528055808 }, { target := 242, numerator := 63374264268889062597722112 }, { target := 243, numerator := 9360047182653730738239700992 }, { target := 245, numerator := 97558206425208174372433428480 }, { target := 253, numerator := 9360047182653730738239700992 }, { target := 260, numerator := 63374264268889062597722112 }, { target := 277, numerator := 1013988228302225001563553792 }, { target := 278, numerator := 149760754922459691811835215872 }, { target := 280, numerator := 1560931302803330789958934855680 }, { target := 288, numerator := 149760754922459691811835215872 }, { target := 295, numerator := 1013988228302225001563553792 }, { target := 312, numerator := 73936641647037239697342464 }, { target := 313, numerator := 10920055046429352527946317824 }, { target := 315, numerator := 113817907496076203434505666560 }, { target := 323, numerator := 10920055046429352527946317824 }, { target := 330, numerator := 73936641647037239697342464 }, { target := 624, numerator := 6517461207258809739226644480 }, { target := 625, numerator := 5069136494534629797176279040 }, { target := 626, numerator := 5793298850896719768201461760 }, { target := 627, numerator := 6807126149803645727636717568 }, { target := 628, numerator := 80382021556191986783795281920 }, { target := 629, numerator := 180750924147977656767885606912 }, { target := 630, numerator := 5069136494534629797176279040 }, { target := 631, numerator := 80382021556191986783795281920 }, { target := 632, numerator := 5793298850896719768201461760 }, { target := 633, numerator := 5648466379624301773996425216 }, { target := 634, numerator := 5648466379624301773996425216 }, { target := 635, numerator := 5648466379624301773996425216 }, { target := 636, numerator := 180750924147977656767885606912 }, { target := 637, numerator := 5648466379624301773996425216 }, { target := 638, numerator := 6517461207258809739226644480 }, { target := 639, numerator := 6807126149803645727636717568 }]

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
    Slot12.Left16.expected,
    Slot12.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 413, numerator := 1922352682822968232130904064 }, { target := 414, numerator := 283921431207163165726604263424 }, { target := 416, numerator := 2959265594897981289297147330560 }, { target := 424, numerator := 283921431207163165726604263424 }, { target := 431, numerator := 1922352682822968232130904064 }, { target := 448, numerator := 1922352682822968232130904064 }, { target := 449, numerator := 283921431207163165726604263424 }, { target := 451, numerator := 2959265594897981289297147330560 }, { target := 459, numerator := 283921431207163165726604263424 }, { target := 466, numerator := 1922352682822968232130904064 }, { target := 509, numerator := 1013988228302225001563553792 }, { target := 510, numerator := 149760754922459691811835215872 }, { target := 512, numerator := 1560931302803330789958934855680 }, { target := 520, numerator := 149760754922459691811835215872 }, { target := 527, numerator := 1013988228302225001563553792 }, { target := 544, numerator := 23723099591320805765747310592 }, { target := 545, numerator := 3503777662040046539681061404672 }, { target := 547, numerator := 36519288605169593273414246727680 }, { target := 555, numerator := 3503777662040046539681061404672 }, { target := 562, numerator := 23723099591320805765747310592 }, { target := 579, numerator := 1901227928066671877931663360 }, { target := 580, numerator := 280801415479611922147191029760 }, { target := 582, numerator := 2926746192756245231173002854400 }, { target := 590, numerator := 280801415479611922147191029760 }, { target := 597, numerator := 1901227928066671877931663360 }, { target := 640, numerator := 887239699764446876368109568 }, { target := 641, numerator := 131040660557152230335355813888 }, { target := 643, numerator := 1365814889952914441214067998720 }, { target := 651, numerator := 131040660557152230335355813888 }, { target := 658, numerator := 887239699764446876368109568 }, { target := 675, numerator := 1922352682822968232130904064 }, { target := 676, numerator := 283921431207163165726604263424 }, { target := 678, numerator := 2959265594897981289297147330560 }, { target := 686, numerator := 283921431207163165726604263424 }, { target := 693, numerator := 1922352682822968232130904064 }, { target := 776, numerator := 73936641647037239697342464 }, { target := 777, numerator := 10920055046429352527946317824 }, { target := 779, numerator := 113817907496076203434505666560 }, { target := 787, numerator := 10920055046429352527946317824 }, { target := 794, numerator := 73936641647037239697342464 }, { target := 811, numerator := 1901227928066671877931663360 }, { target := 812, numerator := 280801415479611922147191029760 }, { target := 814, numerator := 2926746192756245231173002854400 }, { target := 822, numerator := 280801415479611922147191029760 }, { target := 829, numerator := 1901227928066671877931663360 }, { target := 846, numerator := 73936641647037239697342464 }, { target := 847, numerator := 10920055046429352527946317824 }, { target := 849, numerator := 113817907496076203434505666560 }, { target := 857, numerator := 10920055046429352527946317824 }, { target := 864, numerator := 73936641647037239697342464 }, { target := 907, numerator := 1922352682822968232130904064 }, { target := 908, numerator := 283921431207163165726604263424 }, { target := 910, numerator := 2959265594897981289297147330560 }, { target := 918, numerator := 283921431207163165726604263424 }, { target := 925, numerator := 1922352682822968232130904064 }, { target := 942, numerator := 1922352682822968232130904064 }, { target := 943, numerator := 283921431207163165726604263424 }, { target := 945, numerator := 2959265594897981289297147330560 }, { target := 953, numerator := 283921431207163165726604263424 }, { target := 960, numerator := 1922352682822968232130904064 }]

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
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 4573883969335341870401716224 }, { target := 6, numerator := 109478125975703989285099143168 }, { target := 7, numerator := 81887277515519830260417822720 }, { target := 8, numerator := 95018750846837424662538878976 }, { target := 9, numerator := 4573883969335341870401716224 }, { target := 10, numerator := 94871206202665316860267855872 }, { target := 11, numerator := 95313840135181640267080925184 }, { target := 12, numerator := 4573883969335341870401716224 }, { target := 13, numerator := 109478125975703989285099143168 }, { target := 14, numerator := 4573883969335341870401716224 }, { target := 29, numerator := 3938361980752713383808073728 }, { target := 30, numerator := 331094952744372039604362018816 }, { target := 35, numerator := 331094883934251635379252756480 }, { target := 43, numerator := 3938430790873117608917336064 }, { target := 55, numerator := 260250585325010017478246400 }, { target := 56, numerator := 21790556364445826129162403840 }, { target := 61, numerator := 21790564250428917639995719680 }, { target := 69, numerator := 260242699341918506644930560 }, { target := 94, numerator := 16636201942070127297329889280 }, { target := 95, numerator := 398195543258581756600605736960 }, { target := 96, numerator := 297841679930610343548970598400 }, { target := 97, numerator := 345603679054618128370337054720 }, { target := 98, numerator := 16636201942070127297329889280 }, { target := 99, numerator := 345067027379067479102681251840 }, { target := 100, numerator := 346676982405719426905648660480 }, { target := 101, numerator := 16636201942070127297329889280 }, { target := 102, numerator := 398195543258581756600605736960 }, { target := 103, numerator := 16636201942070127297329889280 }, { target := 104, numerator := 137543852985986679295117885440 }, { target := 105, numerator := 11565886801198252055374017331200 }, { target := 110, numerator := 11565884020913361961177306890240 }, { target := 118, numerator := 137546633270876773491828326400 }, { target := 216, numerator := 4573883969335341870401716224 }, { target := 217, numerator := 109478125975703989285099143168 }, { target := 218, numerator := 81887277515519830260417822720 }, { target := 219, numerator := 95018750846837424662538878976 }, { target := 220, numerator := 4573883969335341870401716224 }, { target := 221, numerator := 94871206202665316860267855872 }, { target := 222, numerator := 95313840135181640267080925184 }, { target := 223, numerator := 4573883969335341870401716224 }, { target := 224, numerator := 109478125975703989285099143168 }, { target := 225, numerator := 4573883969335341870401716224 }, { target := 226, numerator := 137345207064801644311423746048 }, { target := 227, numerator := 11549254337956312833240802000896 }, { target := 232, numerator := 11549251551653854780339896975360 }, { target := 240, numerator := 137347993367259697212328771584 }, { target := 624, numerator := 3719237225494969128918712320 }, { target := 625, numerator := 312747838664437698740764016640 }, { target := 630, numerator := 312747763212807132636669542400 }, { target := 638, numerator := 3719312677125535233013186560 }, { target := 1017, numerator := 63374264268889062597722112 }, { target := 1018, numerator := 9360047182653730738239700992 }, { target := 1020, numerator := 97558206425208174372433428480 }, { target := 1028, numerator := 9360047182653730738239700992 }, { target := 1035, numerator := 63374264268889062597722112 }]

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
    Slot15.Left4.expected,
    Slot15.Left5.expected,
    Slot15.Left6.expected,
    Slot15.Left7.expected,
    Slot15.Left8.expected,
    Slot15.Left9.expected,
    Slot15.Left10.expected,
    Slot15.Left11.expected,
    Slot15.Left12.expected,
    Slot15.Left13.expected,
    Slot15.Left14.expected,
    Slot15.Left15.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 10940044363627291531970347008 }, { target := 7, numerator := 105966069265804780982004350976 }, { target := 12, numerator := 10940044363627291531970347008 }, { target := 94, numerator := 39137286391535537041698717696 }, { target := 96, numerator := 379086616360487581993414950912 }, { target := 101, numerator := 39137286391535537041698717696 }, { target := 130, numerator := 2047761184530999874368307200 }, { target := 131, numerator := 171457272446560579279462072320 }, { target := 136, numerator := 171457334496795957219966320640 }, { target := 144, numerator := 2047699134295621933864058880 }, { target := 165, numerator := 246553186097377911295180800 }, { target := 166, numerator := 20643684976843414227627540480 }, { target := 171, numerator := 20643692447774764079995944960 }, { target := 179, numerator := 246545715166028058926776320 }, { target := 216, numerator := 10940040726708539226977206272 }, { target := 218, numerator := 105966034038343939765183709184 }, { target := 223, numerator := 10940040726708539226977206272 }, { target := 226, numerator := 198612288800665539654451200 }, { target := 227, numerator := 16629635120234972572255518720 }, { target := 232, numerator := 16629641138485226619996733440 }, { target := 240, numerator := 198606270550411491913236480 }, { target := 261, numerator := 246553186097377911295180800 }, { target := 262, numerator := 20643684976843414227627540480 }, { target := 267, numerator := 20643692447774764079995944960 }, { target := 275, numerator := 246545715166028058926776320 }, { target := 371, numerator := 246553186097377911295180800 }, { target := 372, numerator := 20643684976843414227627540480 }, { target := 377, numerator := 20643692447774764079995944960 }, { target := 385, numerator := 246545715166028058926776320 }, { target := 397, numerator := 10560694804504353867143577600 }, { target := 398, numerator := 884237839841459576083379650560 }, { target := 403, numerator := 884238159846352394759826309120 }, { target := 411, numerator := 10560374799611535190696919040 }, { target := 432, numerator := 246553186097377911295180800 }, { target := 433, numerator := 20643684976843414227627540480 }, { target := 438, numerator := 20643692447774764079995944960 }, { target := 446, numerator := 246545715166028058926776320 }, { target := 493, numerator := 2047761184530999874368307200 }, { target := 494, numerator := 171457272446560579279462072320 }, { target := 499, numerator := 171457334496795957219966320640 }, { target := 507, numerator := 2047699134295621933864058880 }, { target := 528, numerator := 10560694804504353867143577600 }, { target := 529, numerator := 884237839841459576083379650560 }, { target := 534, numerator := 884238159846352394759826309120 }, { target := 542, numerator := 10560374799611535190696919040 }, { target := 624, numerator := 219158387642113698929049600 }, { target := 625, numerator := 18349942201638590424557813760 }, { target := 630, numerator := 18349948842466456959996395520 }, { target := 638, numerator := 219151746814247163490467840 }, { target := 760, numerator := 246553186097377911295180800 }, { target := 761, numerator := 20643684976843414227627540480 }, { target := 766, numerator := 20643692447774764079995944960 }, { target := 774, numerator := 246545715166028058926776320 }, { target := 795, numerator := 246553186097377911295180800 }, { target := 796, numerator := 20643684976843414227627540480 }, { target := 801, numerator := 20643692447774764079995944960 }, { target := 809, numerator := 246545715166028058926776320 }, { target := 891, numerator := 260250585325010017478246400 }, { target := 892, numerator := 21790556364445826129162403840 }, { target := 897, numerator := 21790564250428917639995719680 }, { target := 905, numerator := 260242699341918506644930560 }]

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
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 9903520314283042199192993792 }, { target := 2, numerator := 9903520314283042199192993792 }, { target := 3, numerator := 9903520314283042199192993792 }, { target := 4, numerator := 9903520314283042199192993792 }, { target := 90, numerator := 9903520314283042199192993792 }, { target := 91, numerator := 9903520314283042199192993792 }, { target := 92, numerator := 9903520314283042199192993792 }, { target := 93, numerator := 9903520314283042199192993792 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent3
