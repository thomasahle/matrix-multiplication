import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk16Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 69; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot3.Left7.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 347, numerator := 802222695012750190754922496 }, { target := 348, numerator := 883877939760180946330976256 }, { target := 349, numerator := 49656064031470839681515520 }, { target := 350, numerator := 3478478447755021920409485312 }, { target := 351, numerator := 1342368930984095032723636224 }, { target := 352, numerator := 802222444828783691069128704 }, { target := 353, numerator := 1342368930984095032723636224 }, { target := 354, numerator := 1342368930984095032723636224 }, { target := 355, numerator := 883877939760180946330976256 }, { target := 356, numerator := 49656064031470839681515520 }, { target := 614, numerator := 18013046457680944467627999232 }, { target := 617, numerator := 64440484386166548927489245184 }, { target := 619, numerator := 18013040469406649539664805888 }, { target := 710, numerator := 13954342594210468706616606720 }, { target := 711, numerator := 8561306323267029776027615232 }, { target := 712, numerator := 480972265352080324495933440 }, { target := 713, numerator := 55815486970036556604280668160 }, { target := 714, numerator := 13002283573351238105540067328 }, { target := 715, numerator := 13954338115110423309016104960 }, { target := 716, numerator := 13002283573351238105540067328 }, { target := 717, numerator := 13002283573351238105540067328 }, { target := 718, numerator := 8561306323267029776027615232 }, { target := 719, numerator := 480972265352080324495933440 }, { target := 736, numerator := 15633964850062706519073357824 }, { target := 739, numerator := 55929477014408702842726514688 }, { target := 741, numerator := 15633959652692563751407190016 }, { target := 881, numerator := 752566630981279351073406976 }, { target := 884, numerator := 2692257433923400292118822912 }, { target := 886, numerator := 752566380797312851387613184 }, { target := 977, numerator := 15609688507127826540006473728 }, { target := 980, numerator := 55842630000411173801045262336 }, { target := 982, numerator := 15609683317828134304588234752 }, { target := 1003, numerator := 15682517535932466477207126016 }, { target := 1006, numerator := 56103171042403760926089019392 }, { target := 1008, numerator := 15682512322421422645045100544 }, { target := 1052, numerator := 802222695012750190754922496 }, { target := 1053, numerator := 883877939760180946330976256 }, { target := 1054, numerator := 49656064031470839681515520 }, { target := 1055, numerator := 3478478447755021920409485312 }, { target := 1056, numerator := 1342368930984095032723636224 }, { target := 1057, numerator := 802222444828783691069128704 }, { target := 1058, numerator := 1342368930984095032723636224 }, { target := 1059, numerator := 1342368930984095032723636224 }, { target := 1060, numerator := 883877939760180946330976256 }, { target := 1061, numerator := 49656064031470839681515520 }, { target := 1078, numerator := 18013046457680944467627999232 }, { target := 1081, numerator := 64440484386166548927489245184 }, { target := 1083, numerator := 18013040469406649539664805888 }, { target := 1092, numerator := 752566630981279351073406976 }, { target := 1095, numerator := 2692257433923400292118822912 }, { target := 1097, numerator := 752566380797312851387613184 }]

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
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 207319341082583203540107264 }, { target := 201, numerator := 246191717535567554203877376 }, { target := 202, numerator := 187883152856091028208222208 }, { target := 203, numerator := 1937140093240386808077877248 }, { target := 204, numerator := 233234258717906103982620672 }, { target := 205, numerator := 187883152856091028208222208 }, { target := 206, numerator := 233234258717906103982620672 }, { target := 207, numerator := 233234258717906103982620672 }, { target := 208, numerator := 9990200748416978120588918784 }, { target := 209, numerator := 233234258717906103982620672 }, { target := 210, numerator := 1937140093240386808077877248 }, { target := 211, numerator := 9990200748416978120588918784 }, { target := 212, numerator := 207319341082583203540107264 }, { target := 213, numerator := 233234258717906103982620672 }, { target := 214, numerator := 233234258717906103982620672 }, { target := 215, numerator := 246191717535567554203877376 }, { target := 296, numerator := 17433326218734085713772412928 }, { target := 297, numerator := 20702074884746726785104740352 }, { target := 298, numerator := 15798951885727765178106249216 }, { target := 299, numerator := 162892641856296613388060983296 }, { target := 300, numerator := 19612491996075846427993964544 }, { target := 301, numerator := 15798951885727765178106249216 }, { target := 302, numerator := 19612491996075846427993964544 }, { target := 303, numerator := 19612491996075846427993964544 }, { target := 304, numerator := 840068407165248755332408147968 }, { target := 305, numerator := 19612491996075846427993964544 }, { target := 306, numerator := 162892641856296613388060983296 }, { target := 307, numerator := 840068407165248755332408147968 }, { target := 308, numerator := 17433326218734085713772412928 }, { target := 309, numerator := 19612491996075846427993964544 }, { target := 310, numerator := 19612491996075846427993964544 }, { target := 311, numerator := 20702074884746726785104740352 }, { target := 659, numerator := 17433322012876436907994644480 }, { target := 660, numerator := 20702069890290768828243640320 }, { target := 661, numerator := 15798948074169270947870146560 }, { target := 662, numerator := 162892602557814207359074959360 }, { target := 663, numerator := 19612487264485991521493975040 }, { target := 664, numerator := 15798948074169270947870146560 }, { target := 665, numerator := 19612487264485991521493975040 }, { target := 666, numerator := 19612487264485991521493975040 }, { target := 667, numerator := 840068204495483303503991930880 }, { target := 668, numerator := 19612487264485991521493975040 }, { target := 669, numerator := 162892602557814207359074959360 }, { target := 670, numerator := 840068204495483303503991930880 }, { target := 671, numerator := 17433322012876436907994644480 }, { target := 672, numerator := 19612487264485991521493975040 }, { target := 673, numerator := 19612487264485991521493975040 }, { target := 674, numerator := 20702069890290768828243640320 }, { target := 1036, numerator := 207323546940232009317875712 }, { target := 1037, numerator := 246196711991525511064977408 }, { target := 1038, numerator := 187886964414585258444324864 }, { target := 1039, numerator := 1937179391722792837063901184 }, { target := 1040, numerator := 233238990307761010482610176 }, { target := 1041, numerator := 187886964414585258444324864 }, { target := 1042, numerator := 233238990307761010482610176 }, { target := 1043, numerator := 233238990307761010482610176 }, { target := 1044, numerator := 9990403418182429949005135872 }, { target := 1045, numerator := 233238990307761010482610176 }, { target := 1046, numerator := 1937179391722792837063901184 }, { target := 1047, numerator := 9990403418182429949005135872 }, { target := 1048, numerator := 207323546940232009317875712 }, { target := 1049, numerator := 233238990307761010482610176 }, { target := 1050, numerator := 233238990307761010482610176 }, { target := 1051, numerator := 246196711991525511064977408 }]

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
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot6.Left10.expected,
    Slot6.Left11.expected,
    Slot6.Left12.expected,
    Slot6.Left13.expected,
    Slot6.Left14.expected,
    Slot6.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 2707986826174021341712220160 }, { target := 202, numerator := 100002350808284873341324492800 }, { target := 205, numerator := 100002326320232115491894722560 }, { target := 212, numerator := 2708011314226779191141990400 }, { target := 296, numerator := 2106211975913127710220615680 }, { target := 298, numerator := 77779606184221568154363494400 }, { target := 301, numerator := 77779587137958312049251450880 }, { target := 308, numerator := 2106231022176383815332659200 }, { target := 331, numerator := 2407099401043574525966417920 }, { target := 333, numerator := 88890978496253220747843993600 }, { target := 336, numerator := 88890956729095213770573086720 }, { target := 343, numerator := 2407121168201581503237324800 }, { target := 467, numerator := 2828341796226200068010541056 }, { target := 469, numerator := 104446899733097534378716692480 }, { target := 472, numerator := 104446874156686876180423376896 }, { target := 479, numerator := 2828367372636858266303856640 }, { target := 563, numerator := 33398504189479596547784048640 }, { target := 565, numerator := 1233362326635513437876335411200 }, { target := 568, numerator := 1233362024616196091066701578240 }, { target := 575, numerator := 33398806208796943357417881600 }, { target := 598, numerator := 75101501312559525210152239104 }, { target := 600, numerator := 2773398529083100487332732600320 }, { target := 603, numerator := 2773397849947770669641880305664 }, { target := 610, numerator := 75102180447889342901004533760 }, { target := 659, numerator := 2106211975913127710220615680 }, { target := 661, numerator := 77779606184221568154363494400 }, { target := 664, numerator := 77779587137958312049251450880 }, { target := 671, numerator := 2106231022176383815332659200 }, { target := 694, numerator := 33398504189479596547784048640 }, { target := 696, numerator := 1233362326635513437876335411200 }, { target := 699, numerator := 1233362024616196091066701578240 }, { target := 706, numerator := 33398806208796943357417881600 }, { target := 720, numerator := 2407099401043574525966417920 }, { target := 722, numerator := 88890978496253220747843993600 }, { target := 725, numerator := 88890956729095213770573086720 }, { target := 732, numerator := 2407121168201581503237324800 }, { target := 830, numerator := 2346921916017485162817257472 }, { target := 832, numerator := 86668704033846890229147893760 }, { target := 835, numerator := 86668682810867833426308759552 }, { target := 842, numerator := 2346943138996541965656391680 }, { target := 865, numerator := 2346921916017485162817257472 }, { target := 867, numerator := 86668704033846890229147893760 }, { target := 870, numerator := 86668682810867833426308759552 }, { target := 877, numerator := 2346943138996541965656391680 }, { target := 926, numerator := 2346921916017485162817257472 }, { target := 928, numerator := 86668704033846890229147893760 }, { target := 931, numerator := 86668682810867833426308759552 }, { target := 938, numerator := 2346943138996541965656391680 }, { target := 961, numerator := 75101501312559525210152239104 }, { target := 963, numerator := 2773398529083100487332732600320 }, { target := 966, numerator := 2773397849947770669641880305664 }, { target := 973, numerator := 75102180447889342901004533760 }, { target := 987, numerator := 2346921916017485162817257472 }, { target := 989, numerator := 86668704033846890229147893760 }, { target := 992, numerator := 86668682810867833426308759552 }, { target := 999, numerator := 2346943138996541965656391680 }, { target := 1036, numerator := 2707986826174021341712220160 }, { target := 1038, numerator := 100002350808284873341324492800 }, { target := 1041, numerator := 100002326320232115491894722560 }, { target := 1048, numerator := 2708011314226779191141990400 }, { target := 1062, numerator := 2828341796226200068010541056 }, { target := 1064, numerator := 104446899733097534378716692480 }, { target := 1067, numerator := 104446874156686876180423376896 }, { target := 1074, numerator := 2828367372636858266303856640 }]

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
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 28796981589167059658342400 }, { target := 72, numerator := 483789290698006602260152320 }, { target := 73, numerator := 1048210129845680971563663360 }, { target := 74, numerator := 34556377907000471590010880 }, { target := 75, numerator := 552902046512007545440174080 }, { target := 76, numerator := 40315774224833883521679360 }, { target := 77, numerator := 1048210129845680971563663360 }, { target := 78, numerator := 1048210129845680971563663360 }, { target := 79, numerator := 552902046512007545440174080 }, { target := 80, numerator := 12935604129853843198527406080 }, { target := 81, numerator := 1036691337210014147700326400 }, { target := 82, numerator := 483789290698006602260152320 }, { target := 83, numerator := 1048210129845680971563663360 }, { target := 84, numerator := 40315774224833883521679360 }, { target := 85, numerator := 1036691337210014147700326400 }, { target := 86, numerator := 40315774224833883521679360 }, { target := 87, numerator := 1048210129845680971563663360 }, { target := 88, numerator := 1048210129845680971563663360 }, { target := 89, numerator := 34556377907000471590010880 }, { target := 146, numerator := 4597357279383833088412876800 }, { target := 147, numerator := 77235602293648395885336330240 }, { target := 148, numerator := 167343804969571524418228715520 }, { target := 149, numerator := 5516828735260599706095452160 }, { target := 150, numerator := 88269259764169595297527234560 }, { target := 151, numerator := 6436300191137366323778027520 }, { target := 152, numerator := 167343804969571524418228715520 }, { target := 153, numerator := 167343804969571524418228715520 }, { target := 154, numerator := 88269259764169595297527234560 }, { target := 155, numerator := 2065132889899217823315064258560 }, { target := 156, numerator := 165504862057817991182863564800 }, { target := 157, numerator := 77235602293648395885336330240 }, { target := 158, numerator := 167343804969571524418228715520 }, { target := 159, numerator := 6436300191137366323778027520 }, { target := 160, numerator := 165504862057817991182863564800 }, { target := 161, numerator := 6436300191137366323778027520 }, { target := 162, numerator := 167343804969571524418228715520 }, { target := 163, numerator := 167343804969571524418228715520 }, { target := 164, numerator := 5516828735260599706095452160 }, { target := 242, numerator := 45874712138307378199973068800 }, { target := 243, numerator := 770695163923563953759547555840 }, { target := 244, numerator := 1669839521834388566479019704320 }, { target := 245, numerator := 55049654565968853839967682560 }, { target := 246, numerator := 880794473055501661439482920960 }, { target := 247, numerator := 64224596993630329479962296320 }, { target := 248, numerator := 1669839521834388566479019704320 }, { target := 249, numerator := 1669839521834388566479019704320 }, { target := 250, numerator := 880794473055501661439482920960 }, { target := 251, numerator := 20606920692527674287427902504960 }, { target := 252, numerator := 1651489636979065615199030476800 }, { target := 253, numerator := 770695163923563953759547555840 }, { target := 254, numerator := 1669839521834388566479019704320 }, { target := 255, numerator := 64224596993630329479962296320 }, { target := 256, numerator := 1651489636979065615199030476800 }, { target := 257, numerator := 64224596993630329479962296320 }, { target := 258, numerator := 1669839521834388566479019704320 }, { target := 259, numerator := 1669839521834388566479019704320 }, { target := 260, numerator := 55049654565968853839967682560 }]

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
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 28999065670494547796295680 }, { target := 72, numerator := 4629619435730386303068405760 }, { target := 74, numerator := 46196639942786728222429020160 }, { target := 82, numerator := 4629619435730386303068405760 }, { target := 89, numerator := 28995756785776326145474560 }, { target := 146, numerator := 487184303264308402977767424 }, { target := 147, numerator := 77777606520270489891549216768 }, { target := 149, numerator := 776103551038817034136807538688 }, { target := 157, numerator := 77777606520270489891549216768 }, { target := 164, numerator := 487128714001042279243972608 }, { target := 181, numerator := 1055565990406001539785162752 }, { target := 182, numerator := 168518147460586061431689969664 }, { target := 184, numerator := 1681557693917436907296416333824 }, { target := 192, numerator := 168518147460586061431689969664 }, { target := 199, numerator := 1055445547002258271695273984 }, { target := 242, numerator := 34798878804593457355554816 }, { target := 243, numerator := 5555543322876463563682086912 }, { target := 245, numerator := 55435967931344073866914824192 }, { target := 253, numerator := 5555543322876463563682086912 }, { target := 260, numerator := 34794908142931591374569472 }, { target := 277, numerator := 556782060873495317688877056 }, { target := 278, numerator := 88888693166023417018913390592 }, { target := 280, numerator := 886975486901505181870637187072 }, { target := 288, numerator := 88888693166023417018913390592 }, { target := 295, numerator := 556718530286905461993111552 }, { target := 640, numerator := 4597357279383833088412876800 }, { target := 641, numerator := 77235602293648395885336330240 }, { target := 642, numerator := 167343804969571524418228715520 }, { target := 643, numerator := 5516828735260599706095452160 }, { target := 644, numerator := 88269259764169595297527234560 }, { target := 645, numerator := 6436300191137366323778027520 }, { target := 646, numerator := 167343804969571524418228715520 }, { target := 647, numerator := 167343804969571524418228715520 }, { target := 648, numerator := 88269259764169595297527234560 }, { target := 649, numerator := 2065132889899217823315064258560 }, { target := 650, numerator := 165504862057817991182863564800 }, { target := 651, numerator := 77235602293648395885336330240 }, { target := 652, numerator := 167343804969571524418228715520 }, { target := 653, numerator := 6436300191137366323778027520 }, { target := 654, numerator := 165504862057817991182863564800 }, { target := 655, numerator := 6436300191137366323778027520 }, { target := 656, numerator := 167343804969571524418228715520 }, { target := 657, numerator := 167343804969571524418228715520 }, { target := 658, numerator := 5516828735260599706095452160 }, { target := 1017, numerator := 28793695762878930144460800 }, { target := 1018, numerator := 483734088816366026426941440 }, { target := 1019, numerator := 1048090525768793057258373120 }, { target := 1020, numerator := 34552434915454716173352960 }, { target := 1021, numerator := 552838958647275458773647360 }, { target := 1022, numerator := 40311174068030502202245120 }, { target := 1023, numerator := 1048090525768793057258373120 }, { target := 1024, numerator := 1048090525768793057258373120 }, { target := 1025, numerator := 552838958647275458773647360 }, { target := 1026, numerator := 12934128136685215420891791360 }, { target := 1027, numerator := 1036573047463641485200588800 }, { target := 1028, numerator := 483734088816366026426941440 }, { target := 1029, numerator := 1048090525768793057258373120 }, { target := 1030, numerator := 40311174068030502202245120 }, { target := 1031, numerator := 1036573047463641485200588800 }, { target := 1032, numerator := 40311174068030502202245120 }, { target := 1033, numerator := 1048090525768793057258373120 }, { target := 1034, numerator := 1048090525768793057258373120 }, { target := 1035, numerator := 34552434915454716173352960 }]

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
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot8.Left10.expected,
    Slot8.Left11.expected,
    Slot8.Left12.expected,
    Slot8.Left13.expected,
    Slot8.Left14.expected,
    Slot8.Left15.expected,
    Slot8.Left16.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 312, numerator := 40598691938692366914813952 }, { target := 313, numerator := 6481467210022540824295768064 }, { target := 315, numerator := 64675295919901419511400628224 }, { target := 323, numerator := 6481467210022540824295768064 }, { target := 330, numerator := 40594059500086856603664384 }, { target := 413, numerator := 1055565990406001539785162752 }, { target := 414, numerator := 168518147460586061431689969664 }, { target := 416, numerator := 1681557693917436907296416333824 }, { target := 424, numerator := 168518147460586061431689969664 }, { target := 431, numerator := 1055445547002258271695273984 }, { target := 448, numerator := 1055565990406001539785162752 }, { target := 449, numerator := 168518147460586061431689969664 }, { target := 451, numerator := 1681557693917436907296416333824 }, { target := 459, numerator := 168518147460586061431689969664 }, { target := 466, numerator := 1055445547002258271695273984 }, { target := 509, numerator := 556782060873495317688877056 }, { target := 510, numerator := 88888693166023417018913390592 }, { target := 512, numerator := 886975486901505181870637187072 }, { target := 520, numerator := 88888693166023417018913390592 }, { target := 527, numerator := 556718530286905461993111552 }, { target := 544, numerator := 13026380299186150870096019456 }, { target := 545, numerator := 2079625050530089527338327867392 }, { target := 547, numerator := 20751530662299798317515115855872 }, { target := 555, numerator := 2079625050530089527338327867392 }, { target := 562, numerator := 13024893948170725704547172352 }, { target := 579, numerator := 1043966364137803720666644480 }, { target := 580, numerator := 166666299686293906910462607360 }, { target := 582, numerator := 1663079037940322216007444725760 }, { target := 590, numerator := 166666299686293906910462607360 }, { target := 597, numerator := 1043847244287947741237084160 }, { target := 640, numerator := 487184303264308402977767424 }, { target := 641, numerator := 77777606520270489891549216768 }, { target := 643, numerator := 776103551038817034136807538688 }, { target := 651, numerator := 77777606520270489891549216768 }, { target := 658, numerator := 487128714001042279243972608 }, { target := 675, numerator := 1055565990406001539785162752 }, { target := 676, numerator := 168518147460586061431689969664 }, { target := 678, numerator := 1681557693917436907296416333824 }, { target := 686, numerator := 168518147460586061431689969664 }, { target := 693, numerator := 1055445547002258271695273984 }, { target := 776, numerator := 40598691938692366914813952 }, { target := 777, numerator := 6481467210022540824295768064 }, { target := 779, numerator := 64675295919901419511400628224 }, { target := 787, numerator := 6481467210022540824295768064 }, { target := 794, numerator := 40594059500086856603664384 }, { target := 811, numerator := 1043966364137803720666644480 }, { target := 812, numerator := 166666299686293906910462607360 }, { target := 814, numerator := 1663079037940322216007444725760 }, { target := 822, numerator := 166666299686293906910462607360 }, { target := 829, numerator := 1043847244287947741237084160 }, { target := 846, numerator := 40598691938692366914813952 }, { target := 847, numerator := 6481467210022540824295768064 }, { target := 849, numerator := 64675295919901419511400628224 }, { target := 857, numerator := 6481467210022540824295768064 }, { target := 864, numerator := 40594059500086856603664384 }, { target := 907, numerator := 1055565990406001539785162752 }, { target := 908, numerator := 168518147460586061431689969664 }, { target := 910, numerator := 1681557693917436907296416333824 }, { target := 918, numerator := 168518147460586061431689969664 }, { target := 925, numerator := 1055445547002258271695273984 }]

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
    Slot8.Left17.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 2616190662574901974196551680 }, { target := 30, numerator := 2034814959780479313263984640 }, { target := 31, numerator := 2325502811177690643730268160 }, { target := 32, numerator := 2732465803133786506383065088 }, { target := 33, numerator := 32266351505090457681757470720 }, { target := 34, numerator := 72555687708743948084384366592 }, { target := 35, numerator := 2034814959780479313263984640 }, { target := 36, numerator := 32266351505090457681757470720 }, { target := 37, numerator := 2325502811177690643730268160 }, { target := 38, numerator := 2267365240898248377637011456 }, { target := 39, numerator := 2267365240898248377637011456 }, { target := 40, numerator := 2267365240898248377637011456 }, { target := 41, numerator := 72555687708743948084384366592 }, { target := 42, numerator := 2267365240898248377637011456 }, { target := 43, numerator := 2616190662574901974196551680 }, { target := 44, numerator := 2732465803133786506383065088 }, { target := 104, numerator := 96612440611393860685686374400 }, { target := 105, numerator := 75143009364417447199978291200 }, { target := 106, numerator := 85877724987905653942832332800 }, { target := 107, numerator := 100906326860789143382827991040 }, { target := 108, numerator := 1191553434207190948456798617600 }, { target := 109, numerator := 2679385019622656403016368783360 }, { target := 110, numerator := 75143009364417447199978291200 }, { target := 111, numerator := 1191553434207190948456798617600 }, { target := 112, numerator := 85877724987905653942832332800 }, { target := 113, numerator := 83730781863208012594261524480 }, { target := 114, numerator := 83730781863208012594261524480 }, { target := 115, numerator := 83730781863208012594261524480 }, { target := 116, numerator := 2679385019622656403016368783360 }, { target := 117, numerator := 83730781863208012594261524480 }, { target := 118, numerator := 96612440611393860685686374400 }, { target := 119, numerator := 100906326860789143382827991040 }, { target := 226, numerator := 96612416953444586153186426880 }, { target := 227, numerator := 75142990963790233674700554240 }, { target := 228, numerator := 85877703958617409913943490560 }, { target := 229, numerator := 100906302151375456648883601408 }, { target := 230, numerator := 1191553142425816562555965931520 }, { target := 231, numerator := 2679384363508863189315036905472 }, { target := 232, numerator := 75142990963790233674700554240 }, { target := 233, numerator := 1191553142425816562555965931520 }, { target := 234, numerator := 85877703958617409913943490560 }, { target := 235, numerator := 83730761359651974666094903296 }, { target := 236, numerator := 83730761359651974666094903296 }, { target := 237, numerator := 83730761359651974666094903296 }, { target := 238, numerator := 2679384363508863189315036905472 }, { target := 239, numerator := 83730761359651974666094903296 }, { target := 240, numerator := 96612416953444586153186426880 }, { target := 241, numerator := 100906302151375456648883601408 }, { target := 942, numerator := 1055565990406001539785162752 }, { target := 943, numerator := 168518147460586061431689969664 }, { target := 945, numerator := 1681557693917436907296416333824 }, { target := 953, numerator := 168518147460586061431689969664 }, { target := 960, numerator := 1055445547002258271695273984 }, { target := 1017, numerator := 34798878804593457355554816 }, { target := 1018, numerator := 5555543322876463563682086912 }, { target := 1020, numerator := 55435967931344073866914824192 }, { target := 1028, numerator := 5555543322876463563682086912 }, { target := 1035, numerator := 34794908142931591374569472 }]

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
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected,
    Slot10.Left8.expected,
    Slot10.Left9.expected,
    Slot10.Left10.expected,
    Slot10.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 210956522505084663251337216 }, { target := 30, numerator := 17739174047132929322785964032 }, { target := 35, numerator := 17739169767488304222169989120 }, { target := 43, numerator := 210960802149709763867312128 }, { target := 55, numerator := 250510870474788037610962944 }, { target := 56, numerator := 21065269180970353570808332288 }, { target := 61, numerator := 21065264098892361263826862080 }, { target := 69, numerator := 250515952552780344592433152 }, { target := 104, numerator := 191179348520232976071524352 }, { target := 105, numerator := 16076126480214217198774779904 }, { target := 110, numerator := 16076122601786275701341552640 }, { target := 118, numerator := 191183226948174473504751616 }, { target := 130, numerator := 1971125007156884822254682112 }, { target := 131, numerator := 165750407502898308359781351424 }, { target := 136, numerator := 165750367514968842575900835840 }, { target := 144, numerator := 1971164995086350606135197696 }, { target := 165, numerator := 237326087818220246157754368 }, { target := 166, numerator := 19956570803024545488134209536 }, { target := 171, numerator := 19956565988424342249941237760 }, { target := 179, numerator := 237330902418423484350726144 }, { target := 226, numerator := 191179348520232976071524352 }, { target := 227, numerator := 16076126480214217198774779904 }, { target := 232, numerator := 16076122601786275701341552640 }, { target := 240, numerator := 191183226948174473504751616 }, { target := 261, numerator := 237326087818220246157754368 }, { target := 262, numerator := 19956570803024545488134209536 }, { target := 267, numerator := 19956565988424342249941237760 }, { target := 275, numerator := 237330902418423484350726144 }, { target := 371, numerator := 237326087818220246157754368 }, { target := 372, numerator := 19956570803024545488134209536 }, { target := 377, numerator := 19956565988424342249941237760 }, { target := 385, numerator := 237330902418423484350726144 }, { target := 397, numerator := 10165467428213767210423812096 }, { target := 398, numerator := 854806449396218031741748641792 }, { target := 403, numerator := 854806243170842659705816350720 }, { target := 411, numerator := 10165673653589139246356103168 }, { target := 432, numerator := 237326087818220246157754368 }, { target := 433, numerator := 19956570803024545488134209536 }, { target := 438, numerator := 19956565988424342249941237760 }, { target := 446, numerator := 237330902418423484350726144 }, { target := 493, numerator := 1971125007156884822254682112 }, { target := 494, numerator := 165750407502898308359781351424 }, { target := 499, numerator := 165750367514968842575900835840 }, { target := 507, numerator := 1971164995086350606135197696 }, { target := 528, numerator := 10165467428213767210423812096 }, { target := 529, numerator := 854806449396218031741748641792 }, { target := 534, numerator := 854806243170842659705816350720 }, { target := 542, numerator := 10165673653589139246356103168 }, { target := 624, numerator := 2616214320524176506696499200 }, { target := 625, numerator := 2034833360407692838541721600 }, { target := 626, numerator := 2325523840465934672619110400 }, { target := 627, numerator := 2732490512547473240327454720 }, { target := 628, numerator := 32266643286464843582590156800 }, { target := 629, numerator := 72556343822537161785716244480 }, { target := 630, numerator := 2034833360407692838541721600 }, { target := 631, numerator := 32266643286464843582590156800 }, { target := 632, numerator := 2325523840465934672619110400 }, { target := 633, numerator := 2267385744454286305803632640 }, { target := 634, numerator := 2267385744454286305803632640 }, { target := 635, numerator := 2267385744454286305803632640 }, { target := 636, numerator := 72556343822537161785716244480 }, { target := 637, numerator := 2267385744454286305803632640 }, { target := 638, numerator := 2616214320524176506696499200 }, { target := 639, numerator := 2732490512547473240327454720 }]

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
    Slot10.Left12.expected,
    Slot10.Left13.expected,
    Slot10.Left14.expected,
    Slot10.Left15.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 802222695012750190754922496 }, { target := 6, numerator := 18013046457680944467627999232 }, { target := 7, numerator := 13954342594210468706616606720 }, { target := 8, numerator := 15633964850062706519073357824 }, { target := 9, numerator := 752566630981279351073406976 }, { target := 10, numerator := 15609688507127826540006473728 }, { target := 11, numerator := 15682517535932466477207126016 }, { target := 12, numerator := 802222695012750190754922496 }, { target := 13, numerator := 18013046457680944467627999232 }, { target := 14, numerator := 752566630981279351073406976 }, { target := 19, numerator := 883877939760180946330976256 }, { target := 21, numerator := 8561306323267029776027615232 }, { target := 26, numerator := 883877939760180946330976256 }, { target := 45, numerator := 49656064031470839681515520 }, { target := 47, numerator := 480972265352080324495933440 }, { target := 52, numerator := 49656064031470839681515520 }, { target := 94, numerator := 3478478447755021920409485312 }, { target := 95, numerator := 64440484386166548927489245184 }, { target := 96, numerator := 55815486970036556604280668160 }, { target := 97, numerator := 55929477014408702842726514688 }, { target := 98, numerator := 2692257433923400292118822912 }, { target := 99, numerator := 55842630000411173801045262336 }, { target := 100, numerator := 56103171042403760926089019392 }, { target := 101, numerator := 3478478447755021920409485312 }, { target := 102, numerator := 64440484386166548927489245184 }, { target := 103, numerator := 2692257433923400292118822912 }, { target := 120, numerator := 1342368930984095032723636224 }, { target := 122, numerator := 13002283573351238105540067328 }, { target := 127, numerator := 1342368930984095032723636224 }, { target := 216, numerator := 802222444828783691069128704 }, { target := 217, numerator := 18013040469406649539664805888 }, { target := 218, numerator := 13954338115110423309016104960 }, { target := 219, numerator := 15633959652692563751407190016 }, { target := 220, numerator := 752566380797312851387613184 }, { target := 221, numerator := 15609683317828134304588234752 }, { target := 222, numerator := 15682512322421422645045100544 }, { target := 223, numerator := 802222444828783691069128704 }, { target := 224, numerator := 18013040469406649539664805888 }, { target := 225, numerator := 752566380797312851387613184 }, { target := 624, numerator := 210956522505084663251337216 }, { target := 625, numerator := 17739174047132929322785964032 }, { target := 630, numerator := 17739169767488304222169989120 }, { target := 638, numerator := 210960802149709763867312128 }, { target := 760, numerator := 237326087818220246157754368 }, { target := 761, numerator := 19956570803024545488134209536 }, { target := 766, numerator := 19956565988424342249941237760 }, { target := 774, numerator := 237330902418423484350726144 }, { target := 795, numerator := 237326087818220246157754368 }, { target := 796, numerator := 19956570803024545488134209536 }, { target := 801, numerator := 19956565988424342249941237760 }, { target := 809, numerator := 237330902418423484350726144 }, { target := 891, numerator := 250510870474788037610962944 }, { target := 892, numerator := 21065269180970353570808332288 }, { target := 897, numerator := 21065264098892361263826862080 }, { target := 905, numerator := 250515952552780344592433152 }]

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
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 361, numerator := 1342368930984095032723636224 }, { target := 363, numerator := 13002283573351238105540067328 }, { target := 368, numerator := 1342368930984095032723636224 }, { target := 387, numerator := 1342368930984095032723636224 }, { target := 389, numerator := 13002283573351238105540067328 }, { target := 394, numerator := 1342368930984095032723636224 }, { target := 483, numerator := 883877939760180946330976256 }, { target := 485, numerator := 8561306323267029776027615232 }, { target := 490, numerator := 883877939760180946330976256 }, { target := 750, numerator := 49656064031470839681515520 }, { target := 752, numerator := 480972265352080324495933440 }, { target := 757, numerator := 49656064031470839681515520 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent3
