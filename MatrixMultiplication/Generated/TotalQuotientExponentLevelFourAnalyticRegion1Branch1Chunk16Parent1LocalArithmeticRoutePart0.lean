import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 67; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent1

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
    Slot3.Left6.expected,
    Slot3.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 94319761198751165869719552 }, { target := 201, numerator := 107419728031911050018291712 }, { target := 202, numerator := 83839787732223258550861824 }, { target := 203, numerator := 1123977154285118059947491328 }, { target := 204, numerator := 99559747932015119529148416 }, { target := 205, numerator := 83839787732223258550861824 }, { target := 206, numerator := 99559747932015119529148416 }, { target := 207, numerator := 96939754565383142699433984 }, { target := 208, numerator := 3662750726551503607940775936 }, { target := 209, numerator := 96939754565383142699433984 }, { target := 210, numerator := 1123977154285118059947491328 }, { target := 211, numerator := 3662750726551503607940775936 }, { target := 212, numerator := 94319761198751165869719552 }, { target := 213, numerator := 96939754565383142699433984 }, { target := 214, numerator := 96939754565383142699433984 }, { target := 215, numerator := 107419728031911050018291712 }, { target := 296, numerator := 18706894585447961759160729600 }, { target := 297, numerator := 21305074388982400892377497600 }, { target := 298, numerator := 16628350742620410452587315200 }, { target := 299, numerator := 222923827143254877629998694400 }, { target := 300, numerator := 19746166506861737412447436800 }, { target := 301, numerator := 16628350742620410452587315200 }, { target := 302, numerator := 19746166506861737412447436800 }, { target := 303, numerator := 19226530546154849585804083200 }, { target := 304, numerator := 726451073068229181647408332800 }, { target := 305, numerator := 19226530546154849585804083200 }, { target := 306, numerator := 222923827143254877629998694400 }, { target := 307, numerator := 726451073068229181647408332800 }, { target := 308, numerator := 18706894585447961759160729600 }, { target := 309, numerator := 19226530546154849585804083200 }, { target := 310, numerator := 19226530546154849585804083200 }, { target := 311, numerator := 21305074388982400892377497600 }, { target := 659, numerator := 18706894585447961759160729600 }, { target := 660, numerator := 21305074388982400892377497600 }, { target := 661, numerator := 16628350742620410452587315200 }, { target := 662, numerator := 222923827143254877629998694400 }, { target := 663, numerator := 19746166506861737412447436800 }, { target := 664, numerator := 16628350742620410452587315200 }, { target := 665, numerator := 19746166506861737412447436800 }, { target := 666, numerator := 19226530546154849585804083200 }, { target := 667, numerator := 726451073068229181647408332800 }, { target := 668, numerator := 19226530546154849585804083200 }, { target := 669, numerator := 222923827143254877629998694400 }, { target := 670, numerator := 726451073068229181647408332800 }, { target := 671, numerator := 18706894585447961759160729600 }, { target := 672, numerator := 19226530546154849585804083200 }, { target := 673, numerator := 19226530546154849585804083200 }, { target := 674, numerator := 21305074388982400892377497600 }, { target := 1036, numerator := 94319761198751165869719552 }, { target := 1037, numerator := 107419728031911050018291712 }, { target := 1038, numerator := 83839787732223258550861824 }, { target := 1039, numerator := 1123977154285118059947491328 }, { target := 1040, numerator := 99559747932015119529148416 }, { target := 1041, numerator := 83839787732223258550861824 }, { target := 1042, numerator := 99559747932015119529148416 }, { target := 1043, numerator := 96939754565383142699433984 }, { target := 1044, numerator := 3662750726551503607940775936 }, { target := 1045, numerator := 96939754565383142699433984 }, { target := 1046, numerator := 1123977154285118059947491328 }, { target := 1047, numerator := 3662750726551503607940775936 }, { target := 1048, numerator := 94319761198751165869719552 }, { target := 1049, numerator := 96939754565383142699433984 }, { target := 1050, numerator := 96939754565383142699433984 }, { target := 1051, numerator := 107419728031911050018291712 }]

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
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left7.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 30352733867483538967756800 }, { target := 72, numerator := 455291008012253084516352000 }, { target := 73, numerator := 799288658510399859484262400 }, { target := 74, numerator := 30352733867483538967756800 }, { target := 75, numerator := 505878897791392316129280000 }, { target := 76, numerator := 30352733867483538967756800 }, { target := 77, numerator := 799288658510399859484262400 }, { target := 78, numerator := 794229869532485936322969600 }, { target := 79, numerator := 505878897791392316129280000 }, { target := 80, numerator := 12257445693485435819812454400 }, { target := 81, numerator := 784112291576658090000384000 }, { target := 82, numerator := 455291008012253084516352000 }, { target := 83, numerator := 799288658510399859484262400 }, { target := 84, numerator := 30352733867483538967756800 }, { target := 85, numerator := 784112291576658090000384000 }, { target := 86, numerator := 30352733867483538967756800 }, { target := 87, numerator := 799288658510399859484262400 }, { target := 88, numerator := 799288658510399859484262400 }, { target := 89, numerator := 30352733867483538967756800 }, { target := 146, numerator := 9777263889536918423706009600 }, { target := 147, numerator := 146658958343053776355590144000 }, { target := 148, numerator := 257467949091138851824258252800 }, { target := 149, numerator := 9777263889536918423706009600 }, { target := 150, numerator := 162954398158948640395100160000 }, { target := 151, numerator := 9777263889536918423706009600 }, { target := 152, numerator := 257467949091138851824258252800 }, { target := 153, numerator := 255838405109549365420307251200 }, { target := 154, numerator := 162954398158948640395100160000 }, { target := 155, numerator := 3948385067391325556773276876800 }, { target := 156, numerator := 252579317146370392612405248000 }, { target := 157, numerator := 146658958343053776355590144000 }, { target := 158, numerator := 257467949091138851824258252800 }, { target := 159, numerator := 9777263889536918423706009600 }, { target := 160, numerator := 252579317146370392612405248000 }, { target := 161, numerator := 9777263889536918423706009600 }, { target := 162, numerator := 257467949091138851824258252800 }, { target := 163, numerator := 257467949091138851824258252800 }, { target := 164, numerator := 9777263889536918423706009600 }, { target := 347, numerator := 2672426522330269274584645632 }, { target := 350, numerator := 9761086817692388474801356800 }, { target := 352, numerator := 2672425621946143447701258240 }, { target := 710, numerator := 120788817022135618247256440832 }, { target := 713, numerator := 441183366392932637896133836800 }, { target := 715, numerator := 120788776326411146351597322240 }, { target := 746, numerator := 9903519133691421481781690368 }, { target := 748, numerator := 9903521494874662916604297216 }, { target := 1013, numerator := 9903519133691421481781690368 }, { target := 1015, numerator := 9903521494874662916604297216 }, { target := 1052, numerator := 2686690070589274799871098880 }, { target := 1055, numerator := 9813184688942033154342912000 }, { target := 1057, numerator := 2686689165399526695606681600 }, { target := 1088, numerator := 9903519133691421481781690368 }, { target := 1090, numerator := 9903521494874662916604297216 }, { target := 1102, numerator := 9903519133691421481781690368 }, { target := 1104, numerator := 9903521494874662916604297216 }]

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
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 1501687378974562513993072640 }, { target := 202, numerator := 58573893188501846972264611840 }, { target := 205, numerator := 58573871703802571749253447680 }, { target := 212, numerator := 1501694540540987588330127360 }, { target := 242, numerator := 103985313081917225145603194880 }, { target := 243, numerator := 1559779696228758377184047923200 }, { target := 244, numerator := 2738279911157153595500884131840 }, { target := 245, numerator := 103985313081917225145603194880 }, { target := 246, numerator := 1733088551365287085760053248000 }, { target := 247, numerator := 103985313081917225145603194880 }, { target := 248, numerator := 2738279911157153595500884131840 }, { target := 249, numerator := 2720949025643500724643283599360 }, { target := 250, numerator := 1733088551365287085760053248000 }, { target := 251, numerator := 41992735599580906087966090199040 }, { target := 252, numerator := 2686287254616194982928082534400 }, { target := 253, numerator := 1559779696228758377184047923200 }, { target := 254, numerator := 2738279911157153595500884131840 }, { target := 255, numerator := 103985313081917225145603194880 }, { target := 256, numerator := 2686287254616194982928082534400 }, { target := 257, numerator := 103985313081917225145603194880 }, { target := 258, numerator := 2738279911157153595500884131840 }, { target := 259, numerator := 2738279911157153595500884131840 }, { target := 260, numerator := 103985313081917225145603194880 }, { target := 640, numerator := 9777293358210576174714716160 }, { target := 641, numerator := 146659400373158642620720742400 }, { target := 642, numerator := 257468725099545172600820858880 }, { target := 643, numerator := 9777293358210576174714716160 }, { target := 644, numerator := 162954889303509602911911936000 }, { target := 645, numerator := 9777293358210576174714716160 }, { target := 646, numerator := 257468725099545172600820858880 }, { target := 647, numerator := 255839176206510076571701739520 }, { target := 648, numerator := 162954889303509602911911936000 }, { target := 649, numerator := 3948396967824037678555626209280 }, { target := 650, numerator := 252580078420439884513463500800 }, { target := 651, numerator := 146659400373158642620720742400 }, { target := 652, numerator := 257468725099545172600820858880 }, { target := 653, numerator := 9777293358210576174714716160 }, { target := 654, numerator := 252580078420439884513463500800 }, { target := 655, numerator := 9777293358210576174714716160 }, { target := 656, numerator := 257468725099545172600820858880 }, { target := 657, numerator := 257468725099545172600820858880 }, { target := 658, numerator := 9777293358210576174714716160 }, { target := 1017, numerator := 30352733867483538967756800 }, { target := 1018, numerator := 455291008012253084516352000 }, { target := 1019, numerator := 799288658510399859484262400 }, { target := 1020, numerator := 30352733867483538967756800 }, { target := 1021, numerator := 505878897791392316129280000 }, { target := 1022, numerator := 30352733867483538967756800 }, { target := 1023, numerator := 799288658510399859484262400 }, { target := 1024, numerator := 794229869532485936322969600 }, { target := 1025, numerator := 505878897791392316129280000 }, { target := 1026, numerator := 12257445693485435819812454400 }, { target := 1027, numerator := 784112291576658090000384000 }, { target := 1028, numerator := 455291008012253084516352000 }, { target := 1029, numerator := 799288658510399859484262400 }, { target := 1030, numerator := 30352733867483538967756800 }, { target := 1031, numerator := 784112291576658090000384000 }, { target := 1032, numerator := 30352733867483538967756800 }, { target := 1033, numerator := 799288658510399859484262400 }, { target := 1034, numerator := 799288658510399859484262400 }, { target := 1035, numerator := 30352733867483538967756800 }]

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
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
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
  [{ target := 29, numerator := 6234430783794035980731678720 }, { target := 30, numerator := 4675823087845526985548759040 }, { target := 31, numerator := 4935591037170278484745912320 }, { target := 32, numerator := 6364314758456411730330255360 }, { target := 33, numerator := 85203887378518491736666275840 }, { target := 34, numerator := 148976918937744984789567406080 }, { target := 35, numerator := 4545939113183151235950182400 }, { target := 36, numerator := 85203887378518491736666275840 }, { target := 37, numerator := 4805707062507902735147335680 }, { target := 38, numerator := 4935591037170278484745912320 }, { target := 39, numerator := 4935591037170278484745912320 }, { target := 40, numerator := 4805707062507902735147335680 }, { target := 41, numerator := 148976918937744984789567406080 }, { target := 42, numerator := 4805707062507902735147335680 }, { target := 43, numerator := 6234430783794035980731678720 }, { target := 44, numerator := 6364314758456411730330255360 }, { target := 296, numerator := 263381857856533289145749995520 }, { target := 298, numerator := 10273310561091879622134590341120 }, { target := 301, numerator := 10273306792877476394467317514240 }, { target := 308, numerator := 263383113928001031701507604480 }, { target := 347, numerator := 4606772438760057708608487424 }, { target := 350, numerator := 16570423466376329979989327872 }, { target := 352, numerator := 4606773975604423349535506432 }, { target := 614, numerator := 111602777468025914166612066304 }, { target := 617, numerator := 401431871717697542418451136512 }, { target := 619, numerator := 111602814699320062435521462272 }, { target := 659, numerator := 263381889433112530362868695040 }, { target := 661, numerator := 10273311792748485137660106506240 }, { target := 664, numerator := 10273308024533630142655213076480 }, { target := 671, numerator := 263383145504730862031166504960 }, { target := 710, numerator := 84556565085628156006394494976 }, { target := 713, numerator := 304147450076391347052062179328 }, { target := 715, numerator := 84556593294158609222119456768 }, { target := 736, numerator := 94215926650770212492186484736 }, { target := 739, numerator := 338891886376857845397201092608 }, { target := 741, numerator := 94215958081716271084048744448 }, { target := 881, numerator := 4606772438760057708608487424 }, { target := 884, numerator := 16570423466376329979989327872 }, { target := 886, numerator := 4606773975604423349535506432 }, { target := 977, numerator := 94215926650770212492186484736 }, { target := 980, numerator := 338891886376857845397201092608 }, { target := 982, numerator := 94215958081716271084048744448 }, { target := 1003, numerator := 94067321088229565469328146432 }, { target := 1006, numerator := 338357356587619899268814340096 }, { target := 1008, numerator := 94067352469599999363095986176 }, { target := 1036, numerator := 1501655802395321296874373120 }, { target := 1038, numerator := 58572661531896331446748446720 }, { target := 1041, numerator := 58572640047648823561357885440 }, { target := 1048, numerator := 1501662963811157258671226880 }, { target := 1052, numerator := 4606772438760057708608487424 }, { target := 1055, numerator := 16570423466376329979989327872 }, { target := 1057, numerator := 4606773975604423349535506432 }, { target := 1078, numerator := 111602777468025914166612066304 }, { target := 1081, numerator := 401431871717697542418451136512 }, { target := 1083, numerator := 111602814699320062435521462272 }, { target := 1092, numerator := 4606772438760057708608487424 }, { target := 1095, numerator := 16570423466376329979989327872 }, { target := 1097, numerator := 4606773975604423349535506432 }]

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
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 97575825250584818224201728 }, { target := 72, numerator := 11532836085040668452038115328 }, { target := 74, numerator := 109444315530219242088151646208 }, { target := 82, numerator := 11532843994883830788680318976 }, { target := 89, numerator := 97575825250584818224201728 }, { target := 104, numerator := 243984199656763452083253805056 }, { target := 105, numerator := 182988149742572589062440353792 }, { target := 106, numerator := 193154158061604399565909262336 }, { target := 107, numerator := 249067203816279357334988259328 }, { target := 108, numerator := 3334450728642433845137802002432 }, { target := 109, numerator := 5830205770964743323739419049984 }, { target := 110, numerator := 177905145583056683810705899520 }, { target := 111, numerator := 3334450728642433845137802002432 }, { target := 112, numerator := 188071153902088494314174808064 }, { target := 113, numerator := 193154158061604399565909262336 }, { target := 114, numerator := 193154158061604399565909262336 }, { target := 115, numerator := 188071153902088494314174808064 }, { target := 116, numerator := 5830205770964743323739419049984 }, { target := 117, numerator := 188071153902088494314174808064 }, { target := 118, numerator := 243984199656763452083253805056 }, { target := 119, numerator := 249067203816279357334988259328 }, { target := 146, numerator := 11532836085040668452038115328 }, { target := 147, numerator := 1363107181751650135143956348928 }, { target := 149, numerator := 12935615437615008337973433335808 }, { target := 157, numerator := 1363108116644328883576872370176 }, { target := 164, numerator := 11532836085040668452038115328 }, { target := 226, numerator := 243984199656763452083253805056 }, { target := 227, numerator := 182988149742572589062440353792 }, { target := 228, numerator := 193154158061604399565909262336 }, { target := 229, numerator := 249067203816279357334988259328 }, { target := 230, numerator := 3334450728642433845137802002432 }, { target := 231, numerator := 5830205770964743323739419049984 }, { target := 232, numerator := 177905145583056683810705899520 }, { target := 233, numerator := 3334450728642433845137802002432 }, { target := 234, numerator := 188071153902088494314174808064 }, { target := 235, numerator := 193154158061604399565909262336 }, { target := 236, numerator := 193154158061604399565909262336 }, { target := 237, numerator := 188071153902088494314174808064 }, { target := 238, numerator := 5830205770964743323739419049984 }, { target := 239, numerator := 188071153902088494314174808064 }, { target := 240, numerator := 243984199656763452083253805056 }, { target := 241, numerator := 249067203816279357334988259328 }, { target := 242, numerator := 109444315530219242088151646208 }, { target := 243, numerator := 12935615437615008337973433335808 }, { target := 245, numerator := 122756411960824267736275105087488 }, { target := 253, numerator := 12935624309560171293489166811136 }, { target := 260, numerator := 109444315530219242088151646208 }, { target := 624, numerator := 6234430783794035980731678720 }, { target := 625, numerator := 4675823087845526985548759040 }, { target := 626, numerator := 4935591037170278484745912320 }, { target := 627, numerator := 6364314758456411730330255360 }, { target := 628, numerator := 85203887378518491736666275840 }, { target := 629, numerator := 148976918937744984789567406080 }, { target := 630, numerator := 4545939113183151235950182400 }, { target := 631, numerator := 85203887378518491736666275840 }, { target := 632, numerator := 4805707062507902735147335680 }, { target := 633, numerator := 4935591037170278484745912320 }, { target := 634, numerator := 4935591037170278484745912320 }, { target := 635, numerator := 4805707062507902735147335680 }, { target := 636, numerator := 148976918937744984789567406080 }, { target := 637, numerator := 4805707062507902735147335680 }, { target := 638, numerator := 6234430783794035980731678720 }, { target := 639, numerator := 6364314758456411730330255360 }]

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
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected,
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot11.Left10.expected,
    Slot11.Left11.expected,
    Slot11.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 6292264093476726481480581120 }, { target := 202, numerator := 246247503920740849597940760576 }, { target := 205, numerator := 246247503920740849597940760576 }, { target := 212, numerator := 6292264093476726481480581120 }, { target := 296, numerator := 4719198070107544861110435840 }, { target := 298, numerator := 184685627940555637198455570432 }, { target := 301, numerator := 184685627940555637198455570432 }, { target := 308, numerator := 4719198070107544861110435840 }, { target := 331, numerator := 4981375740669075131172126720 }, { target := 333, numerator := 194945940603919839265036435456 }, { target := 336, numerator := 194945940603919839265036435456 }, { target := 343, numerator := 4981375740669075131172126720 }, { target := 467, numerator := 6423352928757491616511426560 }, { target := 469, numerator := 251377660252422950631231193088 }, { target := 472, numerator := 251377660252422950631231193088 }, { target := 479, numerator := 6423352928757491616511426560 }, { target := 563, numerator := 85994275944181928580234608640 }, { target := 565, numerator := 3365382553583458277838523727872 }, { target := 568, numerator := 3365382553583458277838523727872 }, { target := 575, numerator := 85994275944181928580234608640 }, { target := 598, numerator := 150358894067037609880379719680 }, { target := 600, numerator := 5884289312439369885184126091264 }, { target := 603, numerator := 5884289312439369885184126091264 }, { target := 610, numerator := 150358894067037609880379719680 }, { target := 640, numerator := 11532843994883830788680318976 }, { target := 641, numerator := 1363108116644328883576872370176 }, { target := 643, numerator := 12935624309560171293489166811136 }, { target := 651, numerator := 1363109051537648832006735265792 }, { target := 658, numerator := 11532843994883830788680318976 }, { target := 659, numerator := 4588109234826779726079590400 }, { target := 661, numerator := 179555471608873536165165137920 }, { target := 664, numerator := 179555471608873536165165137920 }, { target := 671, numerator := 4588109234826779726079590400 }, { target := 694, numerator := 85994275944181928580234608640 }, { target := 696, numerator := 3365382553583458277838523727872 }, { target := 699, numerator := 3365382553583458277838523727872 }, { target := 706, numerator := 85994275944181928580234608640 }, { target := 720, numerator := 4850286905388309996141281280 }, { target := 722, numerator := 189815784272237738231746002944 }, { target := 725, numerator := 189815784272237738231746002944 }, { target := 732, numerator := 4850286905388309996141281280 }, { target := 830, numerator := 4981375740669075131172126720 }, { target := 832, numerator := 194945940603919839265036435456 }, { target := 835, numerator := 194945940603919839265036435456 }, { target := 842, numerator := 4981375740669075131172126720 }, { target := 865, numerator := 4981375740669075131172126720 }, { target := 867, numerator := 194945940603919839265036435456 }, { target := 870, numerator := 194945940603919839265036435456 }, { target := 877, numerator := 4981375740669075131172126720 }, { target := 926, numerator := 4850286905388309996141281280 }, { target := 928, numerator := 189815784272237738231746002944 }, { target := 931, numerator := 189815784272237738231746002944 }, { target := 938, numerator := 4850286905388309996141281280 }, { target := 961, numerator := 150358894067037609880379719680 }, { target := 963, numerator := 5884289312439369885184126091264 }, { target := 966, numerator := 5884289312439369885184126091264 }, { target := 973, numerator := 150358894067037609880379719680 }, { target := 1017, numerator := 97575825250584818224201728 }, { target := 1018, numerator := 11532836085040668452038115328 }, { target := 1020, numerator := 109444315530219242088151646208 }, { target := 1028, numerator := 11532843994883830788680318976 }, { target := 1035, numerator := 97575825250584818224201728 }]

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
    Slot11.Left13.expected,
    Slot11.Left14.expected,
    Slot11.Left15.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 4606772438760057708608487424 }, { target := 6, numerator := 111602777468025914166612066304 }, { target := 7, numerator := 84556565085628156006394494976 }, { target := 8, numerator := 94215926650770212492186484736 }, { target := 9, numerator := 4606772438760057708608487424 }, { target := 10, numerator := 94215926650770212492186484736 }, { target := 11, numerator := 94067321088229565469328146432 }, { target := 12, numerator := 4606772438760057708608487424 }, { target := 13, numerator := 111602777468025914166612066304 }, { target := 14, numerator := 4606772438760057708608487424 }, { target := 29, numerator := 1532563194243198378766761984 }, { target := 30, numerator := 268797185775078833408559808512 }, { target := 35, numerator := 268797218000896152482479079424 }, { target := 43, numerator := 1532530968425879304847491072 }, { target := 71, numerator := 30238732989108013938769920 }, { target := 72, numerator := 9740541771641944082208522240 }, { target := 74, numerator := 103594757915412371717826281472 }, { target := 82, numerator := 9740571129635137390959919104 }, { target := 89, numerator := 30238732989108013938769920 }, { target := 94, numerator := 16570423466376329979989327872 }, { target := 95, numerator := 401431871717697542418451136512 }, { target := 96, numerator := 304147450076391347052062179328 }, { target := 97, numerator := 338891886376857845397201092608 }, { target := 98, numerator := 16570423466376329979989327872 }, { target := 99, numerator := 338891886376857845397201092608 }, { target := 100, numerator := 338357356587619899268814340096 }, { target := 101, numerator := 16570423466376329979989327872 }, { target := 102, numerator := 401431871717697542418451136512 }, { target := 103, numerator := 16570423466376329979989327872 }, { target := 104, numerator := 59778216226022445695058837504 }, { target := 105, numerator := 10484537507207787427449507151872 }, { target := 110, numerator := 10484538764188173617126015238144 }, { target := 118, numerator := 59776959245636256018550751232 }, { target := 216, numerator := 4606773975604423349535506432 }, { target := 217, numerator := 111602814699320062435521462272 }, { target := 218, numerator := 84556593294158609222119456768 }, { target := 219, numerator := 94215958081716271084048744448 }, { target := 220, numerator := 4606773975604423349535506432 }, { target := 221, numerator := 94215958081716271084048744448 }, { target := 222, numerator := 94067352469599999363095986176 }, { target := 223, numerator := 4606773975604423349535506432 }, { target := 224, numerator := 111602814699320062435521462272 }, { target := 225, numerator := 4606773975604423349535506432 }, { target := 226, numerator := 59778194299581690046901649408 }, { target := 227, numerator := 10484533661516078712858234322944 }, { target := 232, numerator := 10484534918496003846522890354688 }, { target := 240, numerator := 59776937319656556382245617664 }, { target := 624, numerator := 1532570503056783594819158016 }, { target := 625, numerator := 268798467672315071605650751488 }, { target := 630, numerator := 268798499898286076016854040576 }, { target := 638, numerator := 1532538277085779183615868928 }, { target := 987, numerator := 4850286905388309996141281280 }, { target := 989, numerator := 189815784272237738231746002944 }, { target := 992, numerator := 189815784272237738231746002944 }, { target := 999, numerator := 4850286905388309996141281280 }, { target := 1036, numerator := 6292264093476726481480581120 }, { target := 1038, numerator := 246247503920740849597940760576 }, { target := 1041, numerator := 246247503920740849597940760576 }, { target := 1048, numerator := 6292264093476726481480581120 }, { target := 1062, numerator := 6423352928757491616511426560 }, { target := 1064, numerator := 251377660252422950631231193088 }, { target := 1067, numerator := 251377660252422950631231193088 }, { target := 1074, numerator := 6423352928757491616511426560 }]

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
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot14.Left10.expected,
    Slot14.Left11.expected,
    Slot14.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 146, numerator := 453580994836620209081548800 }, { target := 147, numerator := 146108126574629161233127833600 }, { target := 149, numerator := 1553921368731185575767394222080 }, { target := 157, numerator := 146108566944527060864398786560 }, { target := 164, numerator := 453580994836620209081548800 }, { target := 181, numerator := 796286635379844367054274560 }, { target := 182, numerator := 256500933319904527498157752320 }, { target := 184, numerator := 2727995291772525788569425412096 }, { target := 192, numerator := 256501706413725284628611203072 }, { target := 199, numerator := 796286635379844367054274560 }, { target := 242, numerator := 30238732989108013938769920 }, { target := 243, numerator := 9740541771641944082208522240 }, { target := 245, numerator := 103594757915412371717826281472 }, { target := 253, numerator := 9740571129635137390959919104 }, { target := 260, numerator := 30238732989108013938769920 }, { target := 277, numerator := 503978883151800232312832000 }, { target := 278, numerator := 162342362860699068036808704000 }, { target := 280, numerator := 1726579298590206195297104691200 }, { target := 288, numerator := 162342852160585623182665318400 }, { target := 295, numerator := 503978883151800232312832000 }, { target := 312, numerator := 30238732989108013938769920 }, { target := 313, numerator := 9740541771641944082208522240 }, { target := 315, numerator := 103594757915412371717826281472 }, { target := 323, numerator := 9740571129635137390959919104 }, { target := 330, numerator := 30238732989108013938769920 }, { target := 413, numerator := 796286635379844367054274560 }, { target := 414, numerator := 256500933319904527498157752320 }, { target := 416, numerator := 2727995291772525788569425412096 }, { target := 424, numerator := 256501706413725284628611203072 }, { target := 431, numerator := 796286635379844367054274560 }, { target := 448, numerator := 791246846548326364731146240 }, { target := 449, numerator := 254877509691297536817789665280 }, { target := 451, numerator := 2710729498786623726616454365184 }, { target := 459, numerator := 254878277892119428396784549888 }, { target := 466, numerator := 791246846548326364731146240 }, { target := 509, numerator := 503978883151800232312832000 }, { target := 510, numerator := 162342362860699068036808704000 }, { target := 512, numerator := 1726579298590206195297104691200 }, { target := 520, numerator := 162342852160585623182665318400 }, { target := 527, numerator := 503978883151800232312832000 }, { target := 544, numerator := 12211408338768119628939919360 }, { target := 545, numerator := 3933555452114738418531874897920 }, { target := 547, numerator := 41835016404840696112048846667776 }, { target := 555, numerator := 3933567307850989649715980664832 }, { target := 562, numerator := 12211408338768119628939919360 }, { target := 579, numerator := 781167268885290360084889600 }, { target := 580, numerator := 251630662434083555457053491200 }, { target := 582, numerator := 2676197912814819602710512271360 }, { target := 590, numerator := 251631420848907715933131243520 }, { target := 597, numerator := 781167268885290360084889600 }, { target := 640, numerator := 453580994836620209081548800 }, { target := 641, numerator := 146108126574629161233127833600 }, { target := 643, numerator := 1553921368731185575767394222080 }, { target := 651, numerator := 146108566944527060864398786560 }, { target := 658, numerator := 453580994836620209081548800 }, { target := 675, numerator := 796286635379844367054274560 }, { target := 676, numerator := 256500933319904527498157752320 }, { target := 678, numerator := 2727995291772525788569425412096 }, { target := 686, numerator := 256501706413725284628611203072 }, { target := 693, numerator := 796286635379844367054274560 }]

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
    Slot14.Left13.expected,
    Slot14.Left14.expected,
    Slot14.Left15.expected,
    Slot14.Left16.expected,
    Slot14.Left17.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left2.expected,
    Slot17.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 9903519133691421481781690368 }, { target := 2, numerator := 9903519133691421481781690368 }, { target := 3, numerator := 9903519133691421481781690368 }, { target := 4, numerator := 9903519133691421481781690368 }, { target := 5, numerator := 2375490242071350466297462784 }, { target := 7, numerator := 107367837353009438442005725184 }, { target := 12, numerator := 2388168951634910933218754560 }, { target := 29, numerator := 94319761198751165869719552 }, { target := 30, numerator := 18706894585447961759160729600 }, { target := 35, numerator := 18706894585447961759160729600 }, { target := 43, numerator := 94319761198751165869719552 }, { target := 55, numerator := 107419728031911050018291712 }, { target := 56, numerator := 21305074388982400892377497600 }, { target := 61, numerator := 21305074388982400892377497600 }, { target := 69, numerator := 107419728031911050018291712 }, { target := 90, numerator := 9903521494874662916604297216 }, { target := 91, numerator := 9903521494874662916604297216 }, { target := 92, numerator := 9903521494874662916604297216 }, { target := 93, numerator := 9903521494874662916604297216 }, { target := 94, numerator := 8676521615726567533156761600 }, { target := 96, numerator := 392162992349273455907674521600 }, { target := 101, numerator := 8722830834615140581638144000 }, { target := 104, numerator := 83839787732223258550861824 }, { target := 105, numerator := 16628350742620410452587315200 }, { target := 110, numerator := 16628350742620410452587315200 }, { target := 118, numerator := 83839787732223258550861824 }, { target := 130, numerator := 1123977154285118059947491328 }, { target := 131, numerator := 222923827143254877629998694400 }, { target := 136, numerator := 222923827143254877629998694400 }, { target := 144, numerator := 1123977154285118059947491328 }, { target := 216, numerator := 2375489441729905286845562880 }, { target := 218, numerator := 107367801179032130090308730880 }, { target := 223, numerator := 2388168147021801507205939200 }, { target := 776, numerator := 30238732989108013938769920 }, { target := 777, numerator := 9740541771641944082208522240 }, { target := 779, numerator := 103594757915412371717826281472 }, { target := 787, numerator := 9740571129635137390959919104 }, { target := 794, numerator := 30238732989108013938769920 }, { target := 811, numerator := 781167268885290360084889600 }, { target := 812, numerator := 251630662434083555457053491200 }, { target := 814, numerator := 2676197912814819602710512271360 }, { target := 822, numerator := 251631420848907715933131243520 }, { target := 829, numerator := 781167268885290360084889600 }, { target := 846, numerator := 30238732989108013938769920 }, { target := 847, numerator := 9740541771641944082208522240 }, { target := 849, numerator := 103594757915412371717826281472 }, { target := 857, numerator := 9740571129635137390959919104 }, { target := 864, numerator := 30238732989108013938769920 }, { target := 907, numerator := 796286635379844367054274560 }, { target := 908, numerator := 256500933319904527498157752320 }, { target := 910, numerator := 2727995291772525788569425412096 }, { target := 918, numerator := 256501706413725284628611203072 }, { target := 925, numerator := 796286635379844367054274560 }, { target := 942, numerator := 796286635379844367054274560 }, { target := 943, numerator := 256500933319904527498157752320 }, { target := 945, numerator := 2727995291772525788569425412096 }, { target := 953, numerator := 256501706413725284628611203072 }, { target := 960, numerator := 796286635379844367054274560 }, { target := 1017, numerator := 30238732989108013938769920 }, { target := 1018, numerator := 9740541771641944082208522240 }, { target := 1020, numerator := 103594757915412371717826281472 }, { target := 1028, numerator := 9740571129635137390959919104 }, { target := 1035, numerator := 30238732989108013938769920 }]

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
    Slot17.Left4.expected,
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
    Slot17.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 165, numerator := 99559747932015119529148416 }, { target := 166, numerator := 19746166506861737412447436800 }, { target := 171, numerator := 19746166506861737412447436800 }, { target := 179, numerator := 99559747932015119529148416 }, { target := 226, numerator := 83839787732223258550861824 }, { target := 227, numerator := 16628350742620410452587315200 }, { target := 232, numerator := 16628350742620410452587315200 }, { target := 240, numerator := 83839787732223258550861824 }, { target := 261, numerator := 99559747932015119529148416 }, { target := 262, numerator := 19746166506861737412447436800 }, { target := 267, numerator := 19746166506861737412447436800 }, { target := 275, numerator := 99559747932015119529148416 }, { target := 371, numerator := 96939754565383142699433984 }, { target := 372, numerator := 19226530546154849585804083200 }, { target := 377, numerator := 19226530546154849585804083200 }, { target := 385, numerator := 96939754565383142699433984 }, { target := 397, numerator := 3662750726551503607940775936 }, { target := 398, numerator := 726451073068229181647408332800 }, { target := 403, numerator := 726451073068229181647408332800 }, { target := 411, numerator := 3662750726551503607940775936 }, { target := 432, numerator := 96939754565383142699433984 }, { target := 433, numerator := 19226530546154849585804083200 }, { target := 438, numerator := 19226530546154849585804083200 }, { target := 446, numerator := 96939754565383142699433984 }, { target := 493, numerator := 1123977154285118059947491328 }, { target := 494, numerator := 222923827143254877629998694400 }, { target := 499, numerator := 222923827143254877629998694400 }, { target := 507, numerator := 1123977154285118059947491328 }, { target := 528, numerator := 3662750726551503607940775936 }, { target := 529, numerator := 726451073068229181647408332800 }, { target := 534, numerator := 726451073068229181647408332800 }, { target := 542, numerator := 3662750726551503607940775936 }, { target := 624, numerator := 94319761198751165869719552 }, { target := 625, numerator := 18706894585447961759160729600 }, { target := 630, numerator := 18706894585447961759160729600 }, { target := 638, numerator := 94319761198751165869719552 }, { target := 760, numerator := 96939754565383142699433984 }, { target := 761, numerator := 19226530546154849585804083200 }, { target := 766, numerator := 19226530546154849585804083200 }, { target := 774, numerator := 96939754565383142699433984 }, { target := 795, numerator := 96939754565383142699433984 }, { target := 796, numerator := 19226530546154849585804083200 }, { target := 801, numerator := 19226530546154849585804083200 }, { target := 809, numerator := 96939754565383142699433984 }, { target := 891, numerator := 107419728031911050018291712 }, { target := 892, numerator := 21305074388982400892377497600 }, { target := 897, numerator := 21305074388982400892377497600 }, { target := 905, numerator := 107419728031911050018291712 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent1
