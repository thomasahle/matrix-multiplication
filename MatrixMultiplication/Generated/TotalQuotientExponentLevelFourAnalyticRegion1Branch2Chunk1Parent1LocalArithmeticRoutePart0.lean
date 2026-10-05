import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 6; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
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
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 2322641404118444525391708160 }, { target := 202, numerator := 81286658313422901871095316480 }, { target := 205, numerator := 81286698181448531175863746560 }, { target := 212, numerator := 2322621470105629873007493120 }, { target := 296, numerator := 2389002587093257226117185536 }, { target := 298, numerator := 83609134265234984781698039808 }, { target := 301, numerator := 83609175272347060638031282176 }, { target := 308, numerator := 2388982083537219297950564352 }, { target := 331, numerator := 2322641404118444525391708160 }, { target := 333, numerator := 81286658313422901871095316480 }, { target := 336, numerator := 81286698181448531175863746560 }, { target := 343, numerator := 2322621470105629873007493120 }, { target := 347, numerator := 446174857675326745477120000 }, { target := 350, numerator := 1525502067993792934313984000 }, { target := 352, numerator := 446174713560138669621248000 }, { target := 467, numerator := 2057196672219193722489798656 }, { target := 469, numerator := 71996754506174570228684423168 }, { target := 472, numerator := 71996789817854413327193604096 }, { target := 479, numerator := 2057179016379272173235208192 }, { target := 563, numerator := 96290076496453228752667672576 }, { target := 565, numerator := 3369912606079332303284551548928 }, { target := 568, numerator := 3369914258893766249605094178816 }, { target := 575, numerator := 96289250089236255592396357632 }, { target := 598, numerator := 26212667275051016786563563520 }, { target := 600, numerator := 917378000965772749688075714560 }, { target := 603, numerator := 917378450904919137556176568320 }, { target := 610, numerator := 26212442305477822852513136640 }, { target := 614, numerator := 8941344147813547979361484800 }, { target := 617, numerator := 30571061442595610403652239360 }, { target := 619, numerator := 8941341259745178939209809920 }, { target := 659, numerator := 2389002587093257226117185536 }, { target := 661, numerator := 83609134265234984781698039808 }, { target := 664, numerator := 83609175272347060638031282176 }, { target := 671, numerator := 2388982083537219297950564352 }, { target := 694, numerator := 96290076496453228752667672576 }, { target := 696, numerator := 3369912606079332303284551548928 }, { target := 699, numerator := 3369914258893766249605094178816 }, { target := 706, numerator := 96289250089236255592396357632 }, { target := 710, numerator := 15009322212197991717850316800 }, { target := 713, numerator := 51317889567311194310322421760 }, { target := 715, numerator := 15009317364163064846058782720 }, { target := 736, numerator := 14402524405759547344001433600 }, { target := 739, numerator := 49243206754839635919655403520 }, { target := 741, numerator := 14402519753721276255373885440 }, { target := 881, numerator := 446174857675326745477120000 }, { target := 884, numerator := 1525502067993792934313984000 }, { target := 886, numerator := 446174713560138669621248000 }, { target := 977, numerator := 14402524405759547344001433600 }, { target := 980, numerator := 49243206754839635919655403520 }, { target := 982, numerator := 14402519753721276255373885440 }, { target := 1003, numerator := 9619529931480044632486707200 }, { target := 1006, numerator := 32889824585946175663809495040 }, { target := 1008, numerator := 9619526824356589717034106880 }, { target := 1052, numerator := 464021851982339815296204800 }, { target := 1055, numerator := 1586522150713544651686543360 }, { target := 1057, numerator := 464021702102544216406097920 }, { target := 1078, numerator := 8941344147813547979361484800 }, { target := 1081, numerator := 30571061442595610403652239360 }, { target := 1083, numerator := 8941341259745178939209809920 }, { target := 1092, numerator := 428327863368313675658035200 }, { target := 1095, numerator := 1464481985274041216941424640 }, { target := 1097, numerator := 428327725017733122836398080 }]

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
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 48001875315091027777290240 }, { target := 72, numerator := 5032910052182131077399183360 }, { target := 74, numerator := 54249739974844387877191680000 }, { target := 82, numerator := 5032913891410741418199613440 }, { target := 89, numerator := 48001875315091027777290240 }, { target := 146, numerator := 1280050008402427407394406400 }, { target := 147, numerator := 134210934724856828730644889600 }, { target := 149, numerator := 1446659732662517010058444800000 }, { target := 157, numerator := 134211037104286437818656358400 }, { target := 164, numerator := 1280050008402427407394406400 }, { target := 181, numerator := 1224047820534821208320901120 }, { target := 182, numerator := 128339206330644342473679175680 }, { target := 184, numerator := 1383368369358531890868387840000 }, { target := 192, numerator := 128339304230973906164090142720 }, { target := 199, numerator := 1224047820534821208320901120 }, { target := 242, numerator := 40001562762575856481075200 }, { target := 243, numerator := 4194091710151775897832652800 }, { target := 245, numerator := 45208116645703656564326400000 }, { target := 253, numerator := 4194094909508951181833011200 }, { target := 260, numerator := 40001562762575856481075200 }, { target := 277, numerator := 1256049070744881893505761280 }, { target := 278, numerator := 131694479698765763191945297920 }, { target := 280, numerator := 1419534862675094816119848960000 }, { target := 288, numerator := 131694580158581067109556551680 }, { target := 295, numerator := 1256049070744881893505761280 }, { target := 312, numerator := 40001562762575856481075200 }, { target := 313, numerator := 4194091710151775897832652800 }, { target := 315, numerator := 45208116645703656564326400000 }, { target := 323, numerator := 4194094909508951181833011200 }, { target := 330, numerator := 40001562762575856481075200 }, { target := 720, numerator := 2322641404118444525391708160 }, { target := 722, numerator := 81286658313422901871095316480 }, { target := 725, numerator := 81286698181448531175863746560 }, { target := 732, numerator := 2322621470105629873007493120 }, { target := 830, numerator := 2322641404118444525391708160 }, { target := 832, numerator := 81286658313422901871095316480 }, { target := 835, numerator := 81286698181448531175863746560 }, { target := 842, numerator := 2322621470105629873007493120 }, { target := 865, numerator := 1990835489244381021764321280 }, { target := 867, numerator := 69674278554362487318081699840 }, { target := 870, numerator := 69674312726955883865026068480 }, { target := 877, numerator := 1990818402947682748292136960 }, { target := 926, numerator := 2322641404118444525391708160 }, { target := 928, numerator := 81286658313422901871095316480 }, { target := 931, numerator := 81286698181448531175863746560 }, { target := 938, numerator := 2322621470105629873007493120 }, { target := 961, numerator := 26212667275051016786563563520 }, { target := 963, numerator := 917378000965772749688075714560 }, { target := 966, numerator := 917378450904919137556176568320 }, { target := 973, numerator := 26212442305477822852513136640 }, { target := 987, numerator := 1990835489244381021764321280 }, { target := 989, numerator := 69674278554362487318081699840 }, { target := 992, numerator := 69674312726955883865026068480 }, { target := 999, numerator := 1990818402947682748292136960 }, { target := 1036, numerator := 2322641404118444525391708160 }, { target := 1038, numerator := 81286658313422901871095316480 }, { target := 1041, numerator := 81286698181448531175863746560 }, { target := 1048, numerator := 2322621470105629873007493120 }, { target := 1062, numerator := 2057196672219193722489798656 }, { target := 1064, numerator := 71996754506174570228684423168 }, { target := 1067, numerator := 71996789817854413327193604096 }, { target := 1074, numerator := 2057179016379272173235208192 }]

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
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot4.Left16.expected,
    Slot4.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 413, numerator := 1224047820534821208320901120 }, { target := 414, numerator := 128339206330644342473679175680 }, { target := 416, numerator := 1383368369358531890868387840000 }, { target := 424, numerator := 128339304230973906164090142720 }, { target := 431, numerator := 1224047820534821208320901120 }, { target := 448, numerator := 696027192068819902770708480 }, { target := 449, numerator := 72977195756640900622288158720 }, { target := 451, numerator := 786621229635243624219279360000 }, { target := 459, numerator := 72977251425455750563894394880 }, { target := 466, numerator := 696027192068819902770708480 }, { target := 509, numerator := 1256049070744881893505761280 }, { target := 510, numerator := 131694479698765763191945297920 }, { target := 512, numerator := 1419534862675094816119848960000 }, { target := 520, numerator := 131694580158581067109556551680 }, { target := 527, numerator := 1256049070744881893505761280 }, { target := 544, numerator := 19608766066214684847023063040 }, { target := 545, numerator := 2055943756316400545117566402560 }, { target := 547, numerator := 22161018779723932447832801280000 }, { target := 555, numerator := 2055945324641287869334542090240 }, { target := 562, numerator := 19608766066214684847023063040 }, { target := 579, numerator := 768030005041456444436643840 }, { target := 580, numerator := 80526560834914097238386933760 }, { target := 582, numerator := 867995839597510206035066880000 }, { target := 590, numerator := 80526622262571862691193815040 }, { target := 597, numerator := 768030005041456444436643840 }, { target := 640, numerator := 1280050008402427407394406400 }, { target := 641, numerator := 134210934724856828730644889600 }, { target := 643, numerator := 1446659732662517010058444800000 }, { target := 651, numerator := 134211037104286437818656358400 }, { target := 658, numerator := 1280050008402427407394406400 }, { target := 675, numerator := 1224047820534821208320901120 }, { target := 676, numerator := 128339206330644342473679175680 }, { target := 678, numerator := 1383368369358531890868387840000 }, { target := 686, numerator := 128339304230973906164090142720 }, { target := 693, numerator := 1224047820534821208320901120 }, { target := 776, numerator := 40001562762575856481075200 }, { target := 777, numerator := 4194091710151775897832652800 }, { target := 779, numerator := 45208116645703656564326400000 }, { target := 787, numerator := 4194094909508951181833011200 }, { target := 794, numerator := 40001562762575856481075200 }, { target := 811, numerator := 768030005041456444436643840 }, { target := 812, numerator := 80526560834914097238386933760 }, { target := 814, numerator := 867995839597510206035066880000 }, { target := 822, numerator := 80526622262571862691193815040 }, { target := 829, numerator := 768030005041456444436643840 }, { target := 846, numerator := 40001562762575856481075200 }, { target := 847, numerator := 4194091710151775897832652800 }, { target := 849, numerator := 45208116645703656564326400000 }, { target := 857, numerator := 4194094909508951181833011200 }, { target := 864, numerator := 40001562762575856481075200 }, { target := 907, numerator := 1232048133087336379617116160 }, { target := 908, numerator := 129178024672674697653245706240 }, { target := 910, numerator := 1392409992687672622181253120000 }, { target := 918, numerator := 129178123212875696400456744960 }, { target := 925, numerator := 1232048133087336379617116160 }, { target := 942, numerator := 696027192068819902770708480 }, { target := 943, numerator := 72977195756640900622288158720 }, { target := 945, numerator := 786621229635243624219279360000 }, { target := 953, numerator := 72977251425455750563894394880 }, { target := 960, numerator := 696027192068819902770708480 }]

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
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot5.Left10.expected,
    Slot5.Left11.expected,
    Slot5.Left12.expected,
    Slot5.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 273947984552642123661312000 }, { target := 30, numerator := 22937427752048238030697267200 }, { target := 35, numerator := 22937436053083071199995494400 }, { target := 43, numerator := 273939683517808954363084800 }, { target := 55, numerator := 268240734874462079418368000 }, { target := 56, numerator := 22459564673880566405057740800 }, { target := 61, numerator := 22459572801977173883328921600 }, { target := 69, numerator := 268232606777854601147187200 }, { target := 104, numerator := 211168238092661636988928000 }, { target := 105, numerator := 17680933892203850148662476800 }, { target := 110, numerator := 17680940290918200716663193600 }, { target := 118, numerator := 211161839378311068988211200 }, { target := 130, numerator := 6637531375723391454543872000 }, { target := 131, numerator := 555754759909002100618769203200 }, { target := 136, numerator := 555754961036158579283224166400 }, { target := 144, numerator := 6637330248566912790088908800 }, { target := 165, numerator := 211168238092661636988928000 }, { target := 166, numerator := 17680933892203850148662476800 }, { target := 171, numerator := 17680940290918200716663193600 }, { target := 179, numerator := 211161839378311068988211200 }, { target := 226, numerator := 211168238092661636988928000 }, { target := 227, numerator := 17680933892203850148662476800 }, { target := 232, numerator := 17680940290918200716663193600 }, { target := 240, numerator := 211161839378311068988211200 }, { target := 261, numerator := 216875487770841681231872000 }, { target := 262, numerator := 18158796970371521774302003200 }, { target := 267, numerator := 18158803542024098033329766400 }, { target := 275, numerator := 216868916118265422204108800 }, { target := 371, numerator := 216875487770841681231872000 }, { target := 372, numerator := 18158796970371521774302003200 }, { target := 377, numerator := 18158803542024098033329766400 }, { target := 385, numerator := 216868916118265422204108800 }, { target := 397, numerator := 3669761543069768448212992000 }, { target := 398, numerator := 307265959261812855286215475200 }, { target := 403, numerator := 307266070461091974616606310400 }, { target := 411, numerator := 3669650343790649117822156800 }, { target := 432, numerator := 199753738736301548503040000 }, { target := 433, numerator := 16725207735868506897383424000 }, { target := 438, numerator := 16725213788706406083330048000 }, { target := 446, numerator := 199747685898402362556416000 }, { target := 493, numerator := 6637531375723391454543872000 }, { target := 494, numerator := 555754759909002100618769203200 }, { target := 499, numerator := 555754961036158579283224166400 }, { target := 507, numerator := 6637330248566912790088908800 }, { target := 528, numerator := 3669761543069768448212992000 }, { target := 529, numerator := 307265959261812855286215475200 }, { target := 534, numerator := 307266070461091974616606310400 }, { target := 542, numerator := 3669650343790649117822156800 }, { target := 624, numerator := 273947984552642123661312000 }, { target := 625, numerator := 22937427752048238030697267200 }, { target := 630, numerator := 22937436053083071199995494400 }, { target := 638, numerator := 273939683517808954363084800 }, { target := 760, numerator := 211168238092661636988928000 }, { target := 761, numerator := 17680933892203850148662476800 }, { target := 766, numerator := 17680940290918200716663193600 }, { target := 774, numerator := 211161839378311068988211200 }, { target := 1017, numerator := 48001875315091027777290240 }, { target := 1018, numerator := 5032910052182131077399183360 }, { target := 1020, numerator := 54249739974844387877191680000 }, { target := 1028, numerator := 5032913891410741418199613440 }, { target := 1035, numerator := 48001875315091027777290240 }]

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
    Slot5.Left14.expected,
    Slot5.Left15.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 262990065170536438714859520 }, { target := 201, numerator := 257511105479483596241633280 }, { target := 202, numerator := 202721508568955171509370880 }, { target := 203, numerator := 6372030120694455796362117120 }, { target := 204, numerator := 202721508568955171509370880 }, { target := 205, numerator := 202721508568955171509370880 }, { target := 206, numerator := 208200468260008013982597120 }, { target := 207, numerator := 208200468260008013982597120 }, { target := 208, numerator := 3522971081346977710284472320 }, { target := 209, numerator := 191763589186849486562918400 }, { target := 210, numerator := 6372030120694455796362117120 }, { target := 211, numerator := 3522971081346977710284472320 }, { target := 212, numerator := 262990065170536438714859520 }, { target := 213, numerator := 202721508568955171509370880 }, { target := 214, numerator := 191763589186849486562918400 }, { target := 215, numerator := 257511105479483596241633280 }, { target := 296, numerator := 22019930641966308509469376512 }, { target := 297, numerator := 21561182086925343748855431168 }, { target := 298, numerator := 16973696536515696142715977728 }, { target := 299, numerator := 533524569512642016594018435072 }, { target := 300, numerator := 16973696536515696142715977728 }, { target := 301, numerator := 16973696536515696142715977728 }, { target := 302, numerator := 17432445091556660903329923072 }, { target := 303, numerator := 17432445091556660903329923072 }, { target := 304, numerator := 294975320891340341074766856192 }, { target := 305, numerator := 16056199426433766621488087040 }, { target := 306, numerator := 533524569512642016594018435072 }, { target := 307, numerator := 294975320891340341074766856192 }, { target := 308, numerator := 22019930641966308509469376512 }, { target := 309, numerator := 16973696536515696142715977728 }, { target := 310, numerator := 16056199426433766621488087040 }, { target := 311, numerator := 21561182086925343748855431168 }, { target := 659, numerator := 22019938610959748351995674624 }, { target := 660, numerator := 21561189889898086927995764736 }, { target := 661, numerator := 16973702679281472687996665856 }, { target := 662, numerator := 533524762594712236111895199744 }, { target := 663, numerator := 16973702679281472687996665856 }, { target := 664, numerator := 16973702679281472687996665856 }, { target := 665, numerator := 17432451400343134111996575744 }, { target := 666, numerator := 17432451400343134111996575744 }, { target := 667, numerator := 294975427642648295631942057984 }, { target := 668, numerator := 16056205237158149839996846080 }, { target := 669, numerator := 533524762594712236111895199744 }, { target := 670, numerator := 294975427642648295631942057984 }, { target := 671, numerator := 22019938610959748351995674624 }, { target := 672, numerator := 16973702679281472687996665856 }, { target := 673, numerator := 16056205237158149839996846080 }, { target := 674, numerator := 21561189889898086927995764736 }, { target := 795, numerator := 199753738736301548503040000 }, { target := 796, numerator := 16725207735868506897383424000 }, { target := 801, numerator := 16725213788706406083330048000 }, { target := 809, numerator := 199747685898402362556416000 }, { target := 891, numerator := 268240734874462079418368000 }, { target := 892, numerator := 22459564673880566405057740800 }, { target := 897, numerator := 22459572801977173883328921600 }, { target := 905, numerator := 268232606777854601147187200 }]

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
    Slot10.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 49126243565714781581082624 }, { target := 72, numerator := 1310033161752394175495536640 }, { target := 73, numerator := 1252719210925726930317606912 }, { target := 74, numerator := 40938536304762317984235520 }, { target := 75, numerator := 1285470039969536784704995328 }, { target := 76, numerator := 40938536304762317984235520 }, { target := 77, numerator := 1252719210925726930317606912 }, { target := 78, numerator := 712330531702864332925698048 }, { target := 79, numerator := 1285470039969536784704995328 }, { target := 80, numerator := 20068070496594488275872251904 }, { target := 81, numerator := 786019897051436505297321984 }, { target := 82, numerator := 1310033161752394175495536640 }, { target := 83, numerator := 1252719210925726930317606912 }, { target := 84, numerator := 40938536304762317984235520 }, { target := 85, numerator := 786019897051436505297321984 }, { target := 86, numerator := 40938536304762317984235520 }, { target := 87, numerator := 1260906918186679393914454016 }, { target := 88, numerator := 712330531702864332925698048 }, { target := 89, numerator := 49126243565714781581082624 }, { target := 146, numerator := 5150798035386397210743668736 }, { target := 147, numerator := 137354614276970592286497832960 }, { target := 148, numerator := 131345349902353128873963552768 }, { target := 149, numerator := 4292331696155331008953057280 }, { target := 150, numerator := 134779215259277393681125998592 }, { target := 151, numerator := 4292331696155331008953057280 }, { target := 152, numerator := 131345349902353128873963552768 }, { target := 153, numerator := 74686571513102759555783196672 }, { target := 154, numerator := 134779215259277393681125998592 }, { target := 155, numerator := 2104100997455343260588788678656 }, { target := 156, numerator := 82412768566182355371898699776 }, { target := 157, numerator := 137354614276970592286497832960 }, { target := 158, numerator := 131345349902353128873963552768 }, { target := 159, numerator := 4292331696155331008953057280 }, { target := 160, numerator := 82412768566182355371898699776 }, { target := 161, numerator := 4292331696155331008953057280 }, { target := 162, numerator := 132203816241584195075754164224 }, { target := 163, numerator := 74686571513102759555783196672 }, { target := 164, numerator := 5150798035386397210743668736 }, { target := 1036, numerator := 262982096177096596188561408 }, { target := 1037, numerator := 257503302506740417101299712 }, { target := 1038, numerator := 202715365803178626228682752 }, { target := 1039, numerator := 6371837038624236278485352448 }, { target := 1040, numerator := 202715365803178626228682752 }, { target := 1041, numerator := 202715365803178626228682752 }, { target := 1042, numerator := 208194159473534805315944448 }, { target := 1043, numerator := 208194159473534805315944448 }, { target := 1044, numerator := 3522864330039023153109270528 }, { target := 1045, numerator := 191757778462466268054159360 }, { target := 1046, numerator := 6371837038624236278485352448 }, { target := 1047, numerator := 3522864330039023153109270528 }, { target := 1048, numerator := 262982096177096596188561408 }, { target := 1049, numerator := 202715365803178626228682752 }, { target := 1050, numerator := 191757778462466268054159360 }, { target := 1051, numerator := 257503302506740417101299712 }]

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
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 242, numerator := 55520454604885787953594368000 }, { target := 243, numerator := 1480545456130287678762516480000 }, { target := 244, numerator := 1415771592424587592816656384000 }, { target := 245, numerator := 46267045504071489961328640000 }, { target := 246, numerator := 1452785228827844784785719296000 }, { target := 247, numerator := 46267045504071489961328640000 }, { target := 248, numerator := 1415771592424587592816656384000 }, { target := 249, numerator := 805046591770843925327118336000 }, { target := 250, numerator := 1452785228827844784785719296000 }, { target := 251, numerator := 22680105706095844379043299328000 }, { target := 252, numerator := 888327273678172607257509888000 }, { target := 253, numerator := 1480545456130287678762516480000 }, { target := 254, numerator := 1415771592424587592816656384000 }, { target := 255, numerator := 46267045504071489961328640000 }, { target := 256, numerator := 888327273678172607257509888000 }, { target := 257, numerator := 46267045504071489961328640000 }, { target := 258, numerator := 1425025001525401890808922112000 }, { target := 259, numerator := 805046591770843925327118336000 }, { target := 260, numerator := 55520454604885787953594368000 }, { target := 640, numerator := 5150801964542884910878162944 }, { target := 641, numerator := 137354719054476930956751011840 }, { target := 642, numerator := 131345450095843565227393155072 }, { target := 643, numerator := 4292334970452404092398469120 }, { target := 644, numerator := 134779318072205488501311930368 }, { target := 645, numerator := 4292334970452404092398469120 }, { target := 646, numerator := 131345450095843565227393155072 }, { target := 647, numerator := 74686628485871831207733362688 }, { target := 648, numerator := 134779318072205488501311930368 }, { target := 649, numerator := 2104102602515768486093729562624 }, { target := 650, numerator := 82412831432686158574050607104 }, { target := 651, numerator := 137354719054476930956751011840 }, { target := 652, numerator := 131345450095843565227393155072 }, { target := 653, numerator := 4292334970452404092398469120 }, { target := 654, numerator := 82412831432686158574050607104 }, { target := 655, numerator := 4292334970452404092398469120 }, { target := 656, numerator := 132203917089934046045872848896 }, { target := 657, numerator := 74686628485871831207733362688 }, { target := 658, numerator := 5150801964542884910878162944 }, { target := 1017, numerator := 49126243565714781581082624 }, { target := 1018, numerator := 1310033161752394175495536640 }, { target := 1019, numerator := 1252719210925726930317606912 }, { target := 1020, numerator := 40938536304762317984235520 }, { target := 1021, numerator := 1285470039969536784704995328 }, { target := 1022, numerator := 40938536304762317984235520 }, { target := 1023, numerator := 1252719210925726930317606912 }, { target := 1024, numerator := 712330531702864332925698048 }, { target := 1025, numerator := 1285470039969536784704995328 }, { target := 1026, numerator := 20068070496594488275872251904 }, { target := 1027, numerator := 786019897051436505297321984 }, { target := 1028, numerator := 1310033161752394175495536640 }, { target := 1029, numerator := 1252719210925726930317606912 }, { target := 1030, numerator := 40938536304762317984235520 }, { target := 1031, numerator := 786019897051436505297321984 }, { target := 1032, numerator := 40938536304762317984235520 }, { target := 1033, numerator := 1260906918186679393914454016 }, { target := 1034, numerator := 712330531702864332925698048 }, { target := 1035, numerator := 49126243565714781581082624 }]

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
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 2294431184635224551399096320 }, { target := 30, numerator := 2359986361339088110010499072 }, { target := 31, numerator := 2294431184635224551399096320 }, { target := 32, numerator := 2032210477819770316953485312 }, { target := 33, numerator := 95120561397306023545145393152 }, { target := 34, numerator := 25894294798026105651504087040 }, { target := 35, numerator := 2359986361339088110010499072 }, { target := 36, numerator := 95120561397306023545145393152 }, { target := 37, numerator := 2294431184635224551399096320 }, { target := 38, numerator := 2294431184635224551399096320 }, { target := 39, numerator := 1966655301115906758342082560 }, { target := 40, numerator := 2294431184635224551399096320 }, { target := 41, numerator := 25894294798026105651504087040 }, { target := 42, numerator := 1966655301115906758342082560 }, { target := 43, numerator := 2294431184635224551399096320 }, { target := 44, numerator := 2032210477819770316953485312 }, { target := 104, numerator := 80299370965486591322053672960 }, { target := 105, numerator := 82593638707357636788398063616 }, { target := 106, numerator := 80299370965486591322053672960 }, { target := 107, numerator := 71122299998002409456676110336 }, { target := 108, numerator := 3328982493454886971665710841856 }, { target := 109, numerator := 906235758039062959206034309120 }, { target := 110, numerator := 82593638707357636788398063616 }, { target := 111, numerator := 3328982493454886971665710841856 }, { target := 112, numerator := 80299370965486591322053672960 }, { target := 113, numerator := 80299370965486591322053672960 }, { target := 114, numerator := 68828032256131363990331719680 }, { target := 115, numerator := 80299370965486591322053672960 }, { target := 116, numerator := 906235758039062959206034309120 }, { target := 117, numerator := 68828032256131363990331719680 }, { target := 118, numerator := 80299370965486591322053672960 }, { target := 119, numerator := 71122299998002409456676110336 }, { target := 226, numerator := 80299410349285188691946373120 }, { target := 227, numerator := 82593679216407622654573412352 }, { target := 228, numerator := 80299410349285188691946373120 }, { target := 229, numerator := 71122334880795452841438216192 }, { target := 230, numerator := 3328984126194651679771833925632 }, { target := 231, numerator := 906236202513361415237680496640 }, { target := 232, numerator := 82593679216407622654573412352 }, { target := 233, numerator := 3328984126194651679771833925632 }, { target := 234, numerator := 80299410349285188691946373120 }, { target := 235, numerator := 80299410349285188691946373120 }, { target := 236, numerator := 68828066013673018878811176960 }, { target := 237, numerator := 80299410349285188691946373120 }, { target := 238, numerator := 906236202513361415237680496640 }, { target := 239, numerator := 68828066013673018878811176960 }, { target := 240, numerator := 80299410349285188691946373120 }, { target := 241, numerator := 71122334880795452841438216192 }, { target := 624, numerator := 2294411492735925866452746240 }, { target := 625, numerator := 2359966106814095176922824704 }, { target := 626, numerator := 2294411492735925866452746240 }, { target := 627, numerator := 2032193036423248624572432384 }, { target := 628, numerator := 95119745027423669492083851264 }, { target := 629, numerator := 25894072560876877635680993280 }, { target := 630, numerator := 2359966106814095176922824704 }, { target := 631, numerator := 95119745027423669492083851264 }, { target := 632, numerator := 2294411492735925866452746240 }, { target := 633, numerator := 2294411492735925866452746240 }, { target := 634, numerator := 1966638422345079314102353920 }, { target := 635, numerator := 2294411492735925866452746240 }, { target := 636, numerator := 25894072560876877635680993280 }, { target := 637, numerator := 1966638422345079314102353920 }, { target := 638, numerator := 2294411492735925866452746240 }, { target := 639, numerator := 2032193036423248624572432384 }]

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
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 624644800745457443667968000 }, { target := 6, numerator := 12517881806938967171106078720 }, { target := 7, numerator := 21013051097077188404990443520 }, { target := 8, numerator := 20163534168063366281602007040 }, { target := 9, numerator := 624644800745457443667968000 }, { target := 10, numerator := 20163534168063366281602007040 }, { target := 11, numerator := 13467341904072062485481390080 }, { target := 12, numerator := 649630592775275741414686720 }, { target := 13, numerator := 12517881806938967171106078720 }, { target := 14, numerator := 599659008715639145921249280 }, { target := 94, numerator := 2135702895191310108039577600 }, { target := 95, numerator := 42799486019633854565113135104 }, { target := 96, numerator := 71845045394235672034451390464 }, { target := 97, numerator := 68940489456775490287517564928 }, { target := 98, numerator := 2135702895191310108039577600 }, { target := 99, numerator := 68940489456775490287517564928 }, { target := 100, numerator := 46045754420324645929333293056 }, { target := 101, numerator := 2221131010998962512361160704 }, { target := 102, numerator := 42799486019633854565113135104 }, { target := 103, numerator := 2050274779383657703717994496 }, { target := 216, numerator := 624644598984194137469747200 }, { target := 217, numerator := 12517877763643250514893733888 }, { target := 218, numerator := 21013044309828290784482295808 }, { target := 219, numerator := 20163527655209786757523439616 }, { target := 220, numerator := 624644598984194137469747200 }, { target := 221, numerator := 20163527655209786757523439616 }, { target := 222, numerator := 13467337554099225603847749632 }, { target := 223, numerator := 649630382943561902968537088 }, { target := 224, numerator := 12517877763643250514893733888 }, { target := 225, numerator := 599658815024826371970957312 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1
