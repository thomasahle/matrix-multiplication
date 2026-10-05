import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent0

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
    Slot0.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 12240373923598120393900032 }, { target := 36, numerator := 13940425857431192670830592 }, { target := 37, numerator := 10880332376531662572355584 }, { target := 38, numerator := 145864455922877601360642048 }, { target := 39, numerator := 12920394697131349304672256 }, { target := 40, numerator := 10880332376531662572355584 }, { target := 41, numerator := 12920394697131349304672256 }, { target := 42, numerator := 12580384310364734849286144 }, { target := 43, numerator := 475334520699727008629784576 }, { target := 44, numerator := 12580384310364734849286144 }, { target := 45, numerator := 145864455922877601360642048 }, { target := 46, numerator := 475334520699727008629784576 }, { target := 47, numerator := 12240373923598120393900032 }, { target := 48, numerator := 12580384310364734849286144 }, { target := 49, numerator := 12580384310364734849286144 }, { target := 50, numerator := 13940425857431192670830592 }, { target := 70, numerator := 255517805655110763222663168 }, { target := 71, numerator := 291006389773876147003588608 }, { target := 72, numerator := 227126938360098456197922816 }, { target := 73, numerator := 3044920517390069928403402752 }, { target := 74, numerator := 269713239302616916735033344 }, { target := 75, numerator := 227126938360098456197922816 }, { target := 76, numerator := 269713239302616916735033344 }, { target := 77, numerator := 262615522478863839978848256 }, { target := 78, numerator := 9922608119606801305146753024 }, { target := 79, numerator := 262615522478863839978848256 }, { target := 80, numerator := 3044920517390069928403402752 }, { target := 81, numerator := 9922608119606801305146753024 }, { target := 82, numerator := 255517805655110763222663168 }, { target := 83, numerator := 262615522478863839978848256 }, { target := 84, numerator := 262615522478863839978848256 }, { target := 85, numerator := 291006389773876147003588608 }, { target := 96, numerator := 13260405083897963760058368 }, { target := 97, numerator := 15102128012217125393399808 }, { target := 98, numerator := 11787026741242634453385216 }, { target := 99, numerator := 158019827249784068140695552 }, { target := 100, numerator := 13997094255225628413394944 }, { target := 101, numerator := 11787026741242634453385216 }, { target := 102, numerator := 13997094255225628413394944 }, { target := 103, numerator := 13628749669561796086726656 }, { target := 104, numerator := 514945730758037592682266624 }, { target := 105, numerator := 13628749669561796086726656 }, { target := 106, numerator := 158019827249784068140695552 }, { target := 107, numerator := 514945730758037592682266624 }, { target := 108, numerator := 13260405083897963760058368 }, { target := 109, numerator := 13628749669561796086726656 }, { target := 110, numerator := 13628749669561796086726656 }, { target := 111, numerator := 15102128012217125393399808 }, { target := 145, numerator := 274898397700807787179671552 }, { target := 146, numerator := 313078730714808868732403712 }, { target := 147, numerator := 244354131289606921937485824 }, { target := 148, numerator := 3275872572601292797224419328 }, { target := 149, numerator := 290170530906408219800764416 }, { target := 150, numerator := 244354131289606921937485824 }, { target := 151, numerator := 290170530906408219800764416 }, { target := 152, numerator := 282534464303608003490217984 }, { target := 153, numerator := 10675221110714702402143911936 }, { target := 154, numerator := 282534464303608003490217984 }, { target := 155, numerator := 3275872572601292797224419328 }, { target := 156, numerator := 10675221110714702402143911936 }, { target := 157, numerator := 274898397700807787179671552 }, { target := 158, numerator := 282534464303608003490217984 }, { target := 159, numerator := 282534464303608003490217984 }, { target := 160, numerator := 313078730714808868732403712 }]

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
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 171, numerator := 411582573180986798244888576 }, { target := 172, numerator := 468746819456123853556678656 }, { target := 173, numerator := 365851176160877153995456512 }, { target := 174, numerator := 4904692330406759345751588864 }, { target := 175, numerator := 434448271691041620369604608 }, { target := 176, numerator := 365851176160877153995456512 }, { target := 177, numerator := 434448271691041620369604608 }, { target := 178, numerator := 423015422436014209307246592 }, { target := 179, numerator := 15983123258528320665176506368 }, { target := 180, numerator := 423015422436014209307246592 }, { target := 181, numerator := 4904692330406759345751588864 }, { target := 182, numerator := 15983123258528320665176506368 }, { target := 183, numerator := 411582573180986798244888576 }, { target := 184, numerator := 423015422436014209307246592 }, { target := 185, numerator := 423015422436014209307246592 }, { target := 186, numerator := 468746819456123853556678656 }, { target := 216, numerator := 12750389503748042076979200 }, { target := 217, numerator := 14521276934824159032115200 }, { target := 218, numerator := 11333679558887148512870400 }, { target := 219, numerator := 151942141586330834750668800 }, { target := 220, numerator := 13458744476178488859033600 }, { target := 221, numerator := 11333679558887148512870400 }, { target := 222, numerator := 13458744476178488859033600 }, { target := 223, numerator := 13104566989963265468006400 }, { target := 224, numerator := 495140125728882300656025600 }, { target := 225, numerator := 13104566989963265468006400 }, { target := 226, numerator := 151942141586330834750668800 }, { target := 227, numerator := 495140125728882300656025600 }, { target := 228, numerator := 12750389503748042076979200 }, { target := 229, numerator := 13104566989963265468006400 }, { target := 230, numerator := 13104566989963265468006400 }, { target := 231, numerator := 14521276934824159032115200 }, { target := 285, numerator := 411582573180986798244888576 }, { target := 286, numerator := 468746819456123853556678656 }, { target := 287, numerator := 365851176160877153995456512 }, { target := 288, numerator := 4904692330406759345751588864 }, { target := 289, numerator := 434448271691041620369604608 }, { target := 290, numerator := 365851176160877153995456512 }, { target := 291, numerator := 434448271691041620369604608 }, { target := 292, numerator := 423015422436014209307246592 }, { target := 293, numerator := 15983123258528320665176506368 }, { target := 294, numerator := 423015422436014209307246592 }, { target := 295, numerator := 4904692330406759345751588864 }, { target := 296, numerator := 15983123258528320665176506368 }, { target := 297, numerator := 411582573180986798244888576 }, { target := 298, numerator := 423015422436014209307246592 }, { target := 299, numerator := 423015422436014209307246592 }, { target := 300, numerator := 468746819456123853556678656 }, { target := 311, numerator := 428923102906084135469580288 }, { target := 312, numerator := 488495756087484709840355328 }, { target := 313, numerator := 381264980360963675972960256 }, { target := 314, numerator := 5111333642964169281012498432 }, { target := 315, numerator := 452752164178644365217890304 }, { target := 316, numerator := 381264980360963675972960256 }, { target := 317, numerator := 452752164178644365217890304 }, { target := 318, numerator := 440837633542364250343735296 }, { target := 319, numerator := 16656513829519600594068701184 }, { target := 320, numerator := 440837633542364250343735296 }, { target := 321, numerator := 5111333642964169281012498432 }, { target := 322, numerator := 16656513829519600594068701184 }, { target := 323, numerator := 428923102906084135469580288 }, { target := 324, numerator := 440837633542364250343735296 }, { target := 325, numerator := 440837633542364250343735296 }, { target := 326, numerator := 488495756087484709840355328 }]

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
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected,
    Slot1.Left6.expected,
    Slot1.Left7.expected,
    Slot1.Left8.expected,
    Slot1.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 6364885973415869192664514560 }, { target := 89, numerator := 23247862589333624422662144000 }, { target := 91, numerator := 6364883828981870623929139200 }, { target := 112, numerator := 7186161582888884572363161600 }, { target := 115, numerator := 26247586794408930799779840000 }, { target := 117, numerator := 7186159161753724897984512000 }, { target := 161, numerator := 6159567071047615347739852800 }, { target := 164, numerator := 22497931538064797828382720000 }, { target := 166, numerator := 6159564995788907055415296000 }, { target := 187, numerator := 81100966435460268745241395200 }, { target := 190, numerator := 296222765251186504740372480000 }, { target := 192, numerator := 81100939111220609562968064000 }, { target := 201, numerator := 7186161582888884572363161600 }, { target := 204, numerator := 26247586794408930799779840000 }, { target := 206, numerator := 7186159161753724897984512000 }, { target := 232, numerator := 6159567071047615347739852800 }, { target := 235, numerator := 22497931538064797828382720000 }, { target := 237, numerator := 6159564995788907055415296000 }, { target := 246, numerator := 7186161582888884572363161600 }, { target := 249, numerator := 26247586794408930799779840000 }, { target := 251, numerator := 7186159161753724897984512000 }, { target := 301, numerator := 7186161582888884572363161600 }, { target := 304, numerator := 26247586794408930799779840000 }, { target := 306, numerator := 7186159161753724897984512000 }, { target := 327, numerator := 297917727336336328985684213760 }, { target := 330, numerator := 1088149955391067388299444224000 }, { target := 332, numerator := 297917626962990137913586483200 }, { target := 341, numerator := 7391480485257138417287823360 }, { target := 344, numerator := 26997517845677757394059264000 }, { target := 346, numerator := 7391477994946688466498355200 }, { target := 356, numerator := 255517805655110763222663168 }, { target := 357, numerator := 291006389773876147003588608 }, { target := 358, numerator := 227126938360098456197922816 }, { target := 359, numerator := 3044920517390069928403402752 }, { target := 360, numerator := 269713239302616916735033344 }, { target := 361, numerator := 227126938360098456197922816 }, { target := 362, numerator := 269713239302616916735033344 }, { target := 363, numerator := 262615522478863839978848256 }, { target := 364, numerator := 9922608119606801305146753024 }, { target := 365, numerator := 262615522478863839978848256 }, { target := 366, numerator := 3044920517390069928403402752 }, { target := 367, numerator := 9922608119606801305146753024 }, { target := 368, numerator := 255517805655110763222663168 }, { target := 369, numerator := 262615522478863839978848256 }, { target := 370, numerator := 262615522478863839978848256 }, { target := 371, numerator := 291006389773876147003588608 }, { target := 427, numerator := 12750389503748042076979200 }, { target := 428, numerator := 14521276934824159032115200 }, { target := 429, numerator := 11333679558887148512870400 }, { target := 430, numerator := 151942141586330834750668800 }, { target := 431, numerator := 13458744476178488859033600 }, { target := 432, numerator := 11333679558887148512870400 }, { target := 433, numerator := 13458744476178488859033600 }, { target := 434, numerator := 13104566989963265468006400 }, { target := 435, numerator := 495140125728882300656025600 }, { target := 436, numerator := 13104566989963265468006400 }, { target := 437, numerator := 151942141586330834750668800 }, { target := 438, numerator := 495140125728882300656025600 }, { target := 439, numerator := 12750389503748042076979200 }, { target := 440, numerator := 13104566989963265468006400 }, { target := 441, numerator := 13104566989963265468006400 }, { target := 442, numerator := 14521276934824159032115200 }]

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
    Slot1.Left10.expected,
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
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot2.Left16.expected,
    Slot2.Left17.expected,
    Slot2.Left18.expected,
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
  [{ target := 122, numerator := 8414122701476110047998115840 }, { target := 124, numerator := 8414124707559528063911854080 }, { target := 197, numerator := 122004779171403595695972679680 }, { target := 199, numerator := 122004808259613156926721884160 }, { target := 211, numerator := 215962482671220157898618306560 }, { target := 213, numerator := 215962534160694553640404254720 }, { target := 215, numerator := 23636917625105229623855153152 }, { target := 242, numerator := 7011768917896758373331763200 }, { target := 244, numerator := 7011770589632940053259878400 }, { target := 256, numerator := 134625963223617760767969853440 }, { target := 258, numerator := 134625995320952449022589665280 }, { target := 260, numerator := 17601959933589000783721922560 }, { target := 261, numerator := 7011768917896758373331763200 }, { target := 263, numerator := 7011770589632940053259878400 }, { target := 265, numerator := 18607786215508372257077460992 }, { target := 337, numerator := 214560128887640806223951953920 }, { target := 339, numerator := 214560180042767965629752279040 }, { target := 351, numerator := 224376605372696267946616422400 }, { target := 353, numerator := 224376658868254081704316108800 }, { target := 355, numerator := 24139830766064915360532922368 }, { target := 372, numerator := 81100966435460268745241395200 }, { target := 375, numerator := 296222765251186504740372480000 }, { target := 377, numerator := 81100939111220609562968064000 }, { target := 382, numerator := 134625963223617760767969853440 }, { target := 384, numerator := 134625995320952449022589665280 }, { target := 386, numerator := 297917727336336328985684213760 }, { target := 389, numerator := 1088149955391067388299444224000 }, { target := 391, numerator := 297917626962990137913586483200 }, { target := 396, numerator := 3437169123552990954607230320640 }, { target := 398, numerator := 3437169943038067214107992391680 }, { target := 400, numerator := 323373149637077928683805605888 }, { target := 401, numerator := 220169544021958212922617364480 }, { target := 403, numerator := 220169596514474317672360181760 }, { target := 405, numerator := 584887982936114511756245598208 }, { target := 406, numerator := 6364885973415869192664514560 }, { target := 409, numerator := 23247862589333624422662144000 }, { target := 411, numerator := 6364883828981870623929139200 }, { target := 416, numerator := 122004779171403595695972679680 }, { target := 418, numerator := 122004808259613156926721884160 }, { target := 420, numerator := 17601959933589000783721922560 }, { target := 421, numerator := 214560128887640806223951953920 }, { target := 423, numerator := 214560180042767965629752279040 }, { target := 425, numerator := 323373149637077928683805605888 }, { target := 443, numerator := 7186161582888884572363161600 }, { target := 446, numerator := 26247586794408930799779840000 }, { target := 448, numerator := 7186159161753724897984512000 }, { target := 453, numerator := 7011768917896758373331763200 }, { target := 455, numerator := 7011770589632940053259878400 }, { target := 457, numerator := 7391480485257138417287823360 }, { target := 460, numerator := 26997517845677757394059264000 }, { target := 462, numerator := 7391477994946688466498355200 }, { target := 467, numerator := 220169544021958212922617364480 }, { target := 469, numerator := 220169596514474317672360181760 }, { target := 472, numerator := 7011768917896758373331763200 }, { target := 474, numerator := 7011770589632940053259878400 }, { target := 477, numerator := 7186161582888884572363161600 }, { target := 480, numerator := 26247586794408930799779840000 }, { target := 482, numerator := 7186159161753724897984512000 }, { target := 487, numerator := 214560128887640806223951953920 }, { target := 489, numerator := 214560180042767965629752279040 }, { target := 492, numerator := 224376605372696267946616422400 }, { target := 494, numerator := 224376658868254081704316108800 }, { target := 498, numerator := 8414122701476110047998115840 }, { target := 500, numerator := 8414124707559528063911854080 }]

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
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 522255954073519803473068032 }, { target := 17, numerator := 7833839311102797052096020480 }, { target := 18, numerator := 13752740123936021491457458176 }, { target := 19, numerator := 522255954073519803473068032 }, { target := 20, numerator := 8704265901225330057884467200 }, { target := 21, numerator := 522255954073519803473068032 }, { target := 22, numerator := 13752740123936021491457458176 }, { target := 23, numerator := 13665697464923768190878613504 }, { target := 24, numerator := 8704265901225330057884467200 }, { target := 25, numerator := 210904362786689747302540640256 }, { target := 26, numerator := 13491612146899261589720924160 }, { target := 27, numerator := 7833839311102797052096020480 }, { target := 28, numerator := 13752740123936021491457458176 }, { target := 29, numerator := 522255954073519803473068032 }, { target := 30, numerator := 13491612146899261589720924160 }, { target := 31, numerator := 522255954073519803473068032 }, { target := 32, numerator := 13752740123936021491457458176 }, { target := 33, numerator := 13752740123936021491457458176 }, { target := 34, numerator := 522255954073519803473068032 }, { target := 35, numerator := 99850852842341915149052411904 }, { target := 37, numerator := 3894720879363016407000520065024 }, { target := 40, numerator := 3894719450793011938312687976448 }, { target := 47, numerator := 99851329032343404711663108096 }, { target := 86, numerator := 857350488433923871425798602752 }, { target := 89, numerator := 3083864211074101602011689517056 }, { target := 91, numerator := 857350774450714378190440103936 }, { target := 126, numerator := 522255954073519803473068032 }, { target := 127, numerator := 7833839311102797052096020480 }, { target := 128, numerator := 13752740123936021491457458176 }, { target := 129, numerator := 522255954073519803473068032 }, { target := 130, numerator := 8704265901225330057884467200 }, { target := 131, numerator := 522255954073519803473068032 }, { target := 132, numerator := 13752740123936021491457458176 }, { target := 133, numerator := 13665697464923768190878613504 }, { target := 134, numerator := 8704265901225330057884467200 }, { target := 135, numerator := 210904362786689747302540640256 }, { target := 136, numerator := 13491612146899261589720924160 }, { target := 137, numerator := 7833839311102797052096020480 }, { target := 138, numerator := 13752740123936021491457458176 }, { target := 139, numerator := 522255954073519803473068032 }, { target := 140, numerator := 13491612146899261589720924160 }, { target := 141, numerator := 522255954073519803473068032 }, { target := 142, numerator := 13752740123936021491457458176 }, { target := 143, numerator := 13752740123936021491457458176 }, { target := 144, numerator := 522255954073519803473068032 }, { target := 145, numerator := 363732758883280204624711122944 }, { target := 147, numerator := 14187536012013886877915901067264 }, { target := 150, numerator := 14187530808075270512377675644928 }, { target := 157, numerator := 363734493529485659804119597056 }, { target := 161, numerator := 34276713455714906340235585519616 }, { target := 164, numerator := 123292318981944537122516655669248 }, { target := 166, numerator := 34276724890613123557714756108288 }, { target := 216, numerator := 99850920008972151607147888640 }, { target := 218, numerator := 3894723499223235241894047907840 }, { target := 221, numerator := 3894722070652269817635725639680 }, { target := 228, numerator := 99851396199293959693255311360 }, { target := 426, numerator := 19110699356468057993755230208 }, { target := 471, numerator := 19110699356468057993755230208 }, { target := 476, numerator := 18607786215508372257077460992 }, { target := 491, numerator := 18607786215508372257077460992 }, { target := 496, numerator := 584887982936114511756245598208 }, { target := 497, numerator := 18607786215508372257077460992 }, { target := 502, numerator := 23636917625105229623855153152 }, { target := 503, numerator := 24139830766064915360532922368 }]

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
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2785365088392105618523029504 }, { target := 1, numerator := 2089023816294079213892272128 }, { target := 2, numerator := 2205080694977083614664065024 }, { target := 3, numerator := 2843393527733607818908925952 }, { target := 4, numerator := 38066656208025443453148069888 }, { target := 5, numerator := 66558619924703023842623225856 }, { target := 6, numerator := 2030995376952577013506375680 }, { target := 7, numerator := 38066656208025443453148069888 }, { target := 8, numerator := 2147052255635581414278168576 }, { target := 9, numerator := 2205080694977083614664065024 }, { target := 10, numerator := 2205080694977083614664065024 }, { target := 11, numerator := 2147052255635581414278168576 }, { target := 12, numerator := 66558619924703023842623225856 }, { target := 13, numerator := 2147052255635581414278168576 }, { target := 14, numerator := 2785365088392105618523029504 }, { target := 15, numerator := 2843393527733607818908925952 }, { target := 16, numerator := 11155850136963874857355837440 }, { target := 17, numerator := 1318549863026772068865083965440 }, { target := 19, numerator := 12512775364822201889707618467840 }, { target := 27, numerator := 1318550767359630123653901844480 }, { target := 34, numerator := 11155850136963874857355837440 }, { target := 35, numerator := 1527539854308352998380415221760 }, { target := 37, numerator := 59780211172771138073998600962048 }, { target := 40, numerator := 59780211172771138073998600962048 }, { target := 47, numerator := 1527539854308352998380415221760 }, { target := 86, numerator := 2680036730481663123358016864256 }, { target := 89, numerator := 9955668581095613427161298370560 }, { target := 91, numerator := 2679472585635433721832262336512 }, { target := 122, numerator := 40910796024243209436005400576 }, { target := 124, numerator := 40910786270350514176705691648 }, { target := 126, numerator := 11155858116252543448051089408 }, { target := 127, numerator := 1318550806127463800163960619008 }, { target := 129, numerator := 12512784314659771894876694642688 }, { target := 137, numerator := 1318551710460968684449259585536 }, { target := 144, numerator := 11155858116252543448051089408 }, { target := 145, numerator := 5475305968930683550391253073920 }, { target := 147, numerator := 214275880354305924632377364054016 }, { target := 150, numerator := 214275880354305924632377364054016 }, { target := 157, numerator := 5475305968930683550391253073920 }, { target := 161, numerator := 104886179789308061881506373566464 }, { target := 164, numerator := 389626019988125876463713533296640 }, { target := 166, numerator := 104864101361391070537084911484928 }, { target := 197, numerator := 6704491549459891004422351749120 }, { target := 199, numerator := 6704489950984732736849979637760 }, { target := 215, numerator := 24642687238626806661468127232 }, { target := 216, numerator := 1527983754787527683296827801600 }, { target := 218, numerator := 59797583200289707972055720263680 }, { target := 221, numerator := 59797583200289707972055720263680 }, { target := 228, numerator := 1527983754787527683296827801600 }, { target := 232, numerator := 34276705079102301282870243622912 }, { target := 235, numerator := 123292288851518099790978441281536 }, { target := 237, numerator := 34276716513997724016780630818816 }, { target := 242, numerator := 69025336404327422993430290104320 }, { target := 244, numerator := 69025319947406757284151673487360 }, { target := 260, numerator := 4887503388645762124138256793600 }, { target := 406, numerator := 857350488433923871425798602752 }, { target := 409, numerator := 3083864211074101602011689517056 }, { target := 411, numerator := 857350774450714378190440103936 }, { target := 416, numerator := 6704491549459891004422351749120 }, { target := 418, numerator := 6704489950984732736849979637760 }, { target := 420, numerator := 4887503388645762124138256793600 }, { target := 498, numerator := 40910796024243209436005400576 }, { target := 500, numerator := 40910786270350514176705691648 }, { target := 502, numerator := 24642687238626806661468127232 }]

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
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left6.expected,
    Slot14.Left14.expected,
    Slot15.Left0.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 11004497558465754153959292928 }, { target := 1, numerator := 1930085484041010516887867490304 }, { target := 6, numerator := 1930085715436968177500482961408 }, { target := 14, numerator := 11004266162508093541343821824 }, { target := 16, numerator := 19154577302423058666760437760 }, { target := 17, numerator := 6170098476004305358981661982720 }, { target := 19, numerator := 65621591993663186111469470089216 }, { target := 27, numerator := 6170117072681298002727940390912 }, { target := 34, numerator := 19154577302423058666760437760 }, { target := 35, numerator := 2706289587543802247850535944192 }, { target := 37, numerator := 105913614172756848722132072398848 }, { target := 40, numerator := 105913653018275415981164165332992 }, { target := 47, numerator := 2706328433062369506882628878336 }, { target := 86, numerator := 1516405408997531959516830105600 }, { target := 89, numerator := 5435395720632334243012490035200 }, { target := 91, numerator := 1516846073825869203133956096000 }, { target := 122, numerator := 30242557624164050215297351680 }, { target := 124, numerator := 30242570098522528482248884224 }, { target := 126, numerator := 19154581869230706807401349120 }, { target := 127, numerator := 6170099947070592289411317104640 }, { target := 129, numerator := 65621607639071772701158583304192 }, { target := 137, numerator := 6170118543752018726990741766144 }, { target := 144, numerator := 19154581869230706807401349120 }, { target := 145, numerator := 10053191402796105354784454737920 }, { target := 147, numerator := 393442682683118151595664584212480 }, { target := 150, numerator := 393442826984539217165299923025920 }, { target := 157, numerator := 10053335704217170924419793551360 }, { target := 161, numerator := 59344465100355937136978826362880 }, { target := 164, numerator := 212713994381574086931134766120960 }, { target := 166, numerator := 59361710500808248802526678220800 }, { target := 197, numerator := 7490545685048856114922090659840 }, { target := 199, numerator := 7490548093101786203129269714944 }, { target := 215, numerator := 11004497558465754153959292928 }, { target := 216, numerator := 2705719916499427143609571344384 }, { target := 218, numerator := 105891319471008357559166300061696 }, { target := 221, numerator := 105891358308349984983911428521984 }, { target := 228, numerator := 2705758753841054568354699804672 }, { target := 232, numerator := 164230683358354509463210516545536 }, { target := 235, numerator := 602340157271298704504302096875520 }, { target := 237, numerator := 164225850322792211850286818394112 }, { target := 242, numerator := 78170322482615044331370977427456 }, { target := 244, numerator := 78170347024119638486425981157376 }, { target := 260, numerator := 1930085484041010516887867490304 }, { target := 406, numerator := 4196480608169705527600163586048 }, { target := 409, numerator := 15391207203326688779627585863680 }, { target := 411, numerator := 4196357120054195435641447120896 }, { target := 416, numerator := 6185785221672362751338219569152 }, { target := 418, numerator := 6185786696478661740517889409024 }, { target := 420, numerator := 1930085715436968177500482961408 }, { target := 498, numerator := 19203217671398231492221992960 }, { target := 500, numerator := 19203222249802648673341931520 }, { target := 502, numerator := 11004266162508093541343821824 }]

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
    Slot19.Left11.expected,
    Slot19.Left18.expected,
    Slot20.Left0.expected,
    Slot20.Left1.expected,
    Slot20.Left2.expected,
    Slot20.Left3.expected,
    Slot20.Left4.expected,
    Slot20.Left5.expected,
    Slot20.Left6.expected,
    Slot20.Left7.expected,
    Slot20.Left8.expected,
    Slot20.Left9.expected,
    Slot20.Left10.expected,
    Slot20.Left11.expected,
    Slot20.Left12.expected,
    Slot20.Left13.expected,
    Slot20.Left14.expected,
    Slot20.Left15.expected,
    Slot21.Left0.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot24.Left5.expected,
    Slot24.Left12.expected,
    Slot25.Left0.expected,
    Slot25.Left1.expected,
    Slot25.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 24046493192530996822884220928 }, { target := 1, numerator := 4769257338920461427586524774400 }, { target := 6, numerator := 4769257338920461427586524774400 }, { target := 14, numerator := 24046493192530996822884220928 }, { target := 16, numerator := 41048278296048155411066388480 }, { target := 17, numerator := 6727022245977519058685893017600 }, { target := 19, numerator := 69257298648605047554618005913600 }, { target := 27, numerator := 6727022245977519058685893017600 }, { target := 34, numerator := 41048278296048155411066388480 }, { target := 35, numerator := 860977474787089141631266324480 }, { target := 37, numerator := 34421719697167366661175341219840 }, { target := 40, numerator := 34421711285117842847523804282880 }, { target := 47, numerator := 860977474787089141631266324480 }, { target := 86, numerator := 98446974419250991913213362176 }, { target := 89, numerator := 358618765788260447793432231936 }, { target := 91, numerator := 98447040641534933306871644160 }, { target := 122, numerator := 522255954073519803473068032 }, { target := 124, numerator := 522255954073519803473068032 }, { target := 126, numerator := 41048268509377136163857367040 }, { target := 127, numerator := 6727020642130624781572951244800 }, { target := 129, numerator := 69257282136380279752221314252800 }, { target := 137, numerator := 6727020642130624781572951244800 }, { target := 144, numerator := 41048268509377136163857367040 }, { target := 145, numerator := 3096910373127396552382810685440 }, { target := 147, numerator := 123813902120264608693744062955520 }, { target := 150, numerator := 123813871862372628416202161520640 }, { target := 157, numerator := 3096910373127396552382810685440 }, { target := 161, numerator := 3839962062078474875794888851456 }, { target := 164, numerator := 13988062746467118696855572054016 }, { target := 166, numerator := 3839964645104103639196064808960 }, { target := 197, numerator := 7833839311102797052096020480 }, { target := 199, numerator := 7833839311102797052096020480 }, { target := 211, numerator := 13752740123936021491457458176 }, { target := 213, numerator := 13752740123936021491457458176 }, { target := 215, numerator := 1856910058928070412348686336 }, { target := 216, numerator := 860977762013862041756515696640 }, { target := 218, numerator := 34421731180440455466399689605120 }, { target := 221, numerator := 34421722768388125347230347427840 }, { target := 228, numerator := 860977762013862041756515696640 }, { target := 232, numerator := 3839960653593813176438344384512 }, { target := 235, numerator := 13988057615694598870727374405632 }, { target := 237, numerator := 3839963236618494495067912273920 }, { target := 260, numerator := 1392682544196052809261514752 }, { target := 265, numerator := 1470053796651389076442710016 }, { target := 355, numerator := 1895595685155738545939283968 }, { target := 400, numerator := 25377770805350295635432046592 }, { target := 405, numerator := 44372413283135349228415483904 }, { target := 406, numerator := 98447443914138225032061517824 }, { target := 409, numerator := 358620476045767056502831448064 }, { target := 411, numerator := 98447510136737981349589155840 }, { target := 416, numerator := 1304780002165273673276315402240 }, { target := 418, numerator := 1304780935416989899233079328768 }, { target := 420, numerator := 1353996917968384675670917120 }, { target := 425, numerator := 25377770805350295635432046592 }, { target := 426, numerator := 1431368170423720942852112384 }, { target := 471, numerator := 1470053796651389076442710016 }, { target := 476, numerator := 1470053796651389076442710016 }, { target := 491, numerator := 1431368170423720942852112384 }, { target := 496, numerator := 44372413283135349228415483904 }, { target := 497, numerator := 1431368170423720942852112384 }, { target := 498, numerator := 11039339952765818723075358720 }, { target := 500, numerator := 11039347848719879808906952704 }, { target := 502, numerator := 1856910058928070412348686336 }, { target := 503, numerator := 1895595685155738545939283968 }]

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
    Slot25.Left3.expected,
    Slot25.Left4.expected,
    Slot25.Left5.expected,
    Slot25.Left6.expected,
    Slot25.Left7.expected,
    Slot25.Left8.expected,
    Slot25.Left9.expected,
    Slot25.Left10.expected,
    Slot25.Left11.expected,
    Slot25.Left12.expected,
    Slot25.Left13.expected,
    Slot25.Left14.expected,
    Slot25.Left15.expected,
    Slot25.Left16.expected,
    Slot25.Left17.expected,
    Slot25.Left18.expected,
    Slot26.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 22727805408755028484476108800 }, { target := 1, numerator := 16924961474604808445886464000 }, { target := 2, numerator := 17892102130296511785651404800 }, { target := 3, numerator := 23211375736600880154358579200 }, { target := 4, numerator := 310935720804882623734428467200 }, { target := 5, numerator := 562392291284725492073313075200 }, { target := 6, numerator := 16924961474604808445886464000 }, { target := 7, numerator := 310935720804882623734428467200 }, { target := 8, numerator := 18375672458142363455533875200 }, { target := 9, numerator := 18375672458142363455533875200 }, { target := 10, numerator := 17892102130296511785651404800 }, { target := 11, numerator := 17892102130296511785651404800 }, { target := 12, numerator := 562392291284725492073313075200 }, { target := 13, numerator := 17892102130296511785651404800 }, { target := 14, numerator := 22727805408755028484476108800 }, { target := 15, numerator := 23211375736600880154358579200 }, { target := 242, numerator := 522255954073519803473068032 }, { target := 244, numerator := 522255954073519803473068032 }, { target := 256, numerator := 8704265901225330057884467200 }, { target := 258, numerator := 8704265901225330057884467200 }, { target := 261, numerator := 522255954073519803473068032 }, { target := 263, numerator := 522255954073519803473068032 }, { target := 337, numerator := 13752740123936021491457458176 }, { target := 339, numerator := 13752740123936021491457458176 }, { target := 351, numerator := 13665697464923768190878613504 }, { target := 353, numerator := 13665697464923768190878613504 }, { target := 382, numerator := 8704265901225330057884467200 }, { target := 384, numerator := 8704265901225330057884467200 }, { target := 396, numerator := 210904362786689747302540640256 }, { target := 398, numerator := 210904362786689747302540640256 }, { target := 401, numerator := 13491612146899261589720924160 }, { target := 403, numerator := 13491612146899261589720924160 }, { target := 416, numerator := 7833839311102797052096020480 }, { target := 418, numerator := 7833839311102797052096020480 }, { target := 421, numerator := 13752740123936021491457458176 }, { target := 423, numerator := 13752740123936021491457458176 }, { target := 453, numerator := 522255954073519803473068032 }, { target := 455, numerator := 522255954073519803473068032 }, { target := 467, numerator := 13491612146899261589720924160 }, { target := 469, numerator := 13491612146899261589720924160 }, { target := 472, numerator := 522255954073519803473068032 }, { target := 474, numerator := 522255954073519803473068032 }, { target := 487, numerator := 13752740123936021491457458176 }, { target := 489, numerator := 13752740123936021491457458176 }, { target := 492, numerator := 13752740123936021491457458176 }, { target := 494, numerator := 13752740123936021491457458176 }, { target := 498, numerator := 522255954073519803473068032 }, { target := 500, numerator := 522255954073519803473068032 }]

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
    Slot27.Left0.expected,
    Slot27.Left2.expected,
    Slot28.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 8414122701476110047998115840 }, { target := 17, numerator := 122004779171403595695972679680 }, { target := 18, numerator := 215962482671220157898618306560 }, { target := 19, numerator := 7011768917896758373331763200 }, { target := 20, numerator := 134625963223617760767969853440 }, { target := 21, numerator := 7011768917896758373331763200 }, { target := 22, numerator := 214560128887640806223951953920 }, { target := 23, numerator := 224376605372696267946616422400 }, { target := 24, numerator := 134625963223617760767969853440 }, { target := 25, numerator := 3437169123552990954607230320640 }, { target := 26, numerator := 220169544021958212922617364480 }, { target := 27, numerator := 122004779171403595695972679680 }, { target := 28, numerator := 214560128887640806223951953920 }, { target := 29, numerator := 7011768917896758373331763200 }, { target := 30, numerator := 220169544021958212922617364480 }, { target := 31, numerator := 7011768917896758373331763200 }, { target := 32, numerator := 214560128887640806223951953920 }, { target := 33, numerator := 224376605372696267946616422400 }, { target := 34, numerator := 8414122701476110047998115840 }, { target := 35, numerator := 6683130272086662652297740288 }, { target := 36, numerator := 7545469662033328800981319680 }, { target := 37, numerator := 6467545424599996115126845440 }, { target := 38, numerator := 85156014757233282182503464960 }, { target := 39, numerator := 7545469662033328800981319680 }, { target := 40, numerator := 6467545424599996115126845440 }, { target := 41, numerator := 7545469662033328800981319680 }, { target := 42, numerator := 7545469662033328800981319680 }, { target := 43, numerator := 312813613703153145434968424448 }, { target := 44, numerator := 7761054509519995338152214528 }, { target := 45, numerator := 85156014757233282182503464960 }, { target := 46, numerator := 312813613703153145434968424448 }, { target := 47, numerator := 6683130272086662652297740288 }, { target := 48, numerator := 7545469662033328800981319680 }, { target := 49, numerator := 7761054509519995338152214528 }, { target := 50, numerator := 7545469662033328800981319680 }, { target := 126, numerator := 8414124707559528063911854080 }, { target := 127, numerator := 122004808259613156926721884160 }, { target := 128, numerator := 215962534160694553640404254720 }, { target := 129, numerator := 7011770589632940053259878400 }, { target := 130, numerator := 134625995320952449022589665280 }, { target := 131, numerator := 7011770589632940053259878400 }, { target := 132, numerator := 214560180042767965629752279040 }, { target := 133, numerator := 224376658868254081704316108800 }, { target := 134, numerator := 134625995320952449022589665280 }, { target := 135, numerator := 3437169943038067214107992391680 }, { target := 136, numerator := 220169596514474317672360181760 }, { target := 137, numerator := 122004808259613156926721884160 }, { target := 138, numerator := 214560180042767965629752279040 }, { target := 139, numerator := 7011770589632940053259878400 }, { target := 140, numerator := 220169596514474317672360181760 }, { target := 141, numerator := 7011770589632940053259878400 }, { target := 142, numerator := 214560180042767965629752279040 }, { target := 143, numerator := 224376658868254081704316108800 }, { target := 144, numerator := 8414124707559528063911854080 }]

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
    Slot28.Left3.expected,
    Slot28.Left5.expected,
    Slot29.Left0.expected,
    Slot29.Left1.expected,
    Slot29.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 12240373923598120393900032 }, { target := 87, numerator := 255517805655110763222663168 }, { target := 88, numerator := 13260405083897963760058368 }, { target := 89, numerator := 274898397700807787179671552 }, { target := 90, numerator := 411582573180986798244888576 }, { target := 91, numerator := 12750389503748042076979200 }, { target := 92, numerator := 411582573180986798244888576 }, { target := 93, numerator := 428923102906084135469580288 }, { target := 94, numerator := 255517805655110763222663168 }, { target := 95, numerator := 12750389503748042076979200 }, { target := 112, numerator := 13940425857431192670830592 }, { target := 113, numerator := 291006389773876147003588608 }, { target := 114, numerator := 15102128012217125393399808 }, { target := 115, numerator := 313078730714808868732403712 }, { target := 116, numerator := 468746819456123853556678656 }, { target := 117, numerator := 14521276934824159032115200 }, { target := 118, numerator := 468746819456123853556678656 }, { target := 119, numerator := 488495756087484709840355328 }, { target := 120, numerator := 291006389773876147003588608 }, { target := 121, numerator := 14521276934824159032115200 }, { target := 145, numerator := 24410255718800305643795251200 }, { target := 146, numerator := 27559966134129377339768832000 }, { target := 147, numerator := 23622828114968037719801856000 }, { target := 148, numerator := 311033903513745829977391104000 }, { target := 149, numerator := 27559966134129377339768832000 }, { target := 150, numerator := 23622828114968037719801856000 }, { target := 151, numerator := 27559966134129377339768832000 }, { target := 152, numerator := 27559966134129377339768832000 }, { target := 153, numerator := 1142557453160620757714416435200 }, { target := 154, numerator := 28347393737961645263762227200 }, { target := 155, numerator := 311033903513745829977391104000 }, { target := 156, numerator := 1142557453160620757714416435200 }, { target := 157, numerator := 24410255718800305643795251200 }, { target := 158, numerator := 27559966134129377339768832000 }, { target := 159, numerator := 28347393737961645263762227200 }, { target := 160, numerator := 27559966134129377339768832000 }, { target := 161, numerator := 10880332376531662572355584 }, { target := 162, numerator := 227126938360098456197922816 }, { target := 163, numerator := 11787026741242634453385216 }, { target := 164, numerator := 244354131289606921937485824 }, { target := 165, numerator := 365851176160877153995456512 }, { target := 166, numerator := 11333679558887148512870400 }, { target := 167, numerator := 365851176160877153995456512 }, { target := 168, numerator := 381264980360963675972960256 }, { target := 169, numerator := 227126938360098456197922816 }, { target := 170, numerator := 11333679558887148512870400 }, { target := 216, numerator := 6683128020430964155125596160 }, { target := 217, numerator := 7545467119841411142883737600 }, { target := 218, numerator := 6467543245578352408186060800 }, { target := 219, numerator := 85155986066781640041116467200 }, { target := 220, numerator := 7545467119841411142883737600 }, { target := 221, numerator := 6467543245578352408186060800 }, { target := 222, numerator := 7545467119841411142883737600 }, { target := 223, numerator := 7545467119841411142883737600 }, { target := 224, numerator := 312813508311139644809265807360 }, { target := 225, numerator := 7761051894694022889823272960 }, { target := 226, numerator := 85155986066781640041116467200 }, { target := 227, numerator := 312813508311139644809265807360 }, { target := 228, numerator := 6683128020430964155125596160 }, { target := 229, numerator := 7545467119841411142883737600 }, { target := 230, numerator := 7761051894694022889823272960 }, { target := 231, numerator := 7545467119841411142883737600 }]

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
    Slot29.Left3.expected,
    Slot29.Left4.expected,
    Slot29.Left5.expected,
    Slot29.Left6.expected,
    Slot29.Left7.expected,
    Slot29.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 187, numerator := 145864455922877601360642048 }, { target := 188, numerator := 3044920517390069928403402752 }, { target := 189, numerator := 158019827249784068140695552 }, { target := 190, numerator := 3275872572601292797224419328 }, { target := 191, numerator := 4904692330406759345751588864 }, { target := 192, numerator := 151942141586330834750668800 }, { target := 193, numerator := 4904692330406759345751588864 }, { target := 194, numerator := 5111333642964169281012498432 }, { target := 195, numerator := 3044920517390069928403402752 }, { target := 196, numerator := 151942141586330834750668800 }, { target := 201, numerator := 12920394697131349304672256 }, { target := 202, numerator := 269713239302616916735033344 }, { target := 203, numerator := 13997094255225628413394944 }, { target := 204, numerator := 290170530906408219800764416 }, { target := 205, numerator := 434448271691041620369604608 }, { target := 206, numerator := 13458744476178488859033600 }, { target := 207, numerator := 434448271691041620369604608 }, { target := 208, numerator := 452752164178644365217890304 }, { target := 209, numerator := 269713239302616916735033344 }, { target := 210, numerator := 13458744476178488859033600 }, { target := 232, numerator := 10880332376531662572355584 }, { target := 233, numerator := 227126938360098456197922816 }, { target := 234, numerator := 11787026741242634453385216 }, { target := 235, numerator := 244354131289606921937485824 }, { target := 236, numerator := 365851176160877153995456512 }, { target := 237, numerator := 11333679558887148512870400 }, { target := 238, numerator := 365851176160877153995456512 }, { target := 239, numerator := 381264980360963675972960256 }, { target := 240, numerator := 227126938360098456197922816 }, { target := 241, numerator := 11333679558887148512870400 }, { target := 246, numerator := 12920394697131349304672256 }, { target := 247, numerator := 269713239302616916735033344 }, { target := 248, numerator := 13997094255225628413394944 }, { target := 249, numerator := 290170530906408219800764416 }, { target := 250, numerator := 434448271691041620369604608 }, { target := 251, numerator := 13458744476178488859033600 }, { target := 252, numerator := 434448271691041620369604608 }, { target := 253, numerator := 452752164178644365217890304 }, { target := 254, numerator := 269713239302616916735033344 }, { target := 255, numerator := 13458744476178488859033600 }, { target := 301, numerator := 12580384310364734849286144 }, { target := 302, numerator := 262615522478863839978848256 }, { target := 303, numerator := 13628749669561796086726656 }, { target := 304, numerator := 282534464303608003490217984 }, { target := 305, numerator := 423015422436014209307246592 }, { target := 306, numerator := 13104566989963265468006400 }, { target := 307, numerator := 423015422436014209307246592 }, { target := 308, numerator := 440837633542364250343735296 }, { target := 309, numerator := 262615522478863839978848256 }, { target := 310, numerator := 13104566989963265468006400 }, { target := 327, numerator := 475334520699727008629784576 }, { target := 328, numerator := 9922608119606801305146753024 }, { target := 329, numerator := 514945730758037592682266624 }, { target := 330, numerator := 10675221110714702402143911936 }, { target := 331, numerator := 15983123258528320665176506368 }, { target := 332, numerator := 495140125728882300656025600 }, { target := 333, numerator := 15983123258528320665176506368 }, { target := 334, numerator := 16656513829519600594068701184 }, { target := 335, numerator := 9922608119606801305146753024 }, { target := 336, numerator := 495140125728882300656025600 }]

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
    Slot29.Left9.expected,
    Slot29.Left10.expected,
    Slot29.Left11.expected,
    Slot29.Left12.expected,
    Slot29.Left13.expected,
    Slot29.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 341, numerator := 12580384310364734849286144 }, { target := 342, numerator := 262615522478863839978848256 }, { target := 343, numerator := 13628749669561796086726656 }, { target := 344, numerator := 282534464303608003490217984 }, { target := 345, numerator := 423015422436014209307246592 }, { target := 346, numerator := 13104566989963265468006400 }, { target := 347, numerator := 423015422436014209307246592 }, { target := 348, numerator := 440837633542364250343735296 }, { target := 349, numerator := 262615522478863839978848256 }, { target := 350, numerator := 13104566989963265468006400 }, { target := 372, numerator := 145864455922877601360642048 }, { target := 373, numerator := 3044920517390069928403402752 }, { target := 374, numerator := 158019827249784068140695552 }, { target := 375, numerator := 3275872572601292797224419328 }, { target := 376, numerator := 4904692330406759345751588864 }, { target := 377, numerator := 151942141586330834750668800 }, { target := 378, numerator := 4904692330406759345751588864 }, { target := 379, numerator := 5111333642964169281012498432 }, { target := 380, numerator := 3044920517390069928403402752 }, { target := 381, numerator := 151942141586330834750668800 }, { target := 386, numerator := 475334520699727008629784576 }, { target := 387, numerator := 9922608119606801305146753024 }, { target := 388, numerator := 514945730758037592682266624 }, { target := 389, numerator := 10675221110714702402143911936 }, { target := 390, numerator := 15983123258528320665176506368 }, { target := 391, numerator := 495140125728882300656025600 }, { target := 392, numerator := 15983123258528320665176506368 }, { target := 393, numerator := 16656513829519600594068701184 }, { target := 394, numerator := 9922608119606801305146753024 }, { target := 395, numerator := 495140125728882300656025600 }, { target := 406, numerator := 12240373923598120393900032 }, { target := 407, numerator := 255517805655110763222663168 }, { target := 408, numerator := 13260405083897963760058368 }, { target := 409, numerator := 274898397700807787179671552 }, { target := 410, numerator := 411582573180986798244888576 }, { target := 411, numerator := 12750389503748042076979200 }, { target := 412, numerator := 411582573180986798244888576 }, { target := 413, numerator := 428923102906084135469580288 }, { target := 414, numerator := 255517805655110763222663168 }, { target := 415, numerator := 12750389503748042076979200 }, { target := 443, numerator := 12580384310364734849286144 }, { target := 444, numerator := 262615522478863839978848256 }, { target := 445, numerator := 13628749669561796086726656 }, { target := 446, numerator := 282534464303608003490217984 }, { target := 447, numerator := 423015422436014209307246592 }, { target := 448, numerator := 13104566989963265468006400 }, { target := 449, numerator := 423015422436014209307246592 }, { target := 450, numerator := 440837633542364250343735296 }, { target := 451, numerator := 262615522478863839978848256 }, { target := 452, numerator := 13104566989963265468006400 }, { target := 457, numerator := 12580384310364734849286144 }, { target := 458, numerator := 262615522478863839978848256 }, { target := 459, numerator := 13628749669561796086726656 }, { target := 460, numerator := 282534464303608003490217984 }, { target := 461, numerator := 423015422436014209307246592 }, { target := 462, numerator := 13104566989963265468006400 }, { target := 463, numerator := 423015422436014209307246592 }, { target := 464, numerator := 440837633542364250343735296 }, { target := 465, numerator := 262615522478863839978848256 }, { target := 466, numerator := 13104566989963265468006400 }]

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
    Slot29.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 477, numerator := 13940425857431192670830592 }, { target := 478, numerator := 291006389773876147003588608 }, { target := 479, numerator := 15102128012217125393399808 }, { target := 480, numerator := 313078730714808868732403712 }, { target := 481, numerator := 468746819456123853556678656 }, { target := 482, numerator := 14521276934824159032115200 }, { target := 483, numerator := 468746819456123853556678656 }, { target := 484, numerator := 488495756087484709840355328 }, { target := 485, numerator := 291006389773876147003588608 }, { target := 486, numerator := 14521276934824159032115200 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent0
