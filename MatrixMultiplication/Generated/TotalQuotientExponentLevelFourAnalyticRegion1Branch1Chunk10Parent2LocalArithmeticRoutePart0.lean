import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 44; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent2

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
  [{ target := 26, numerator := 4760145414732602375405568 }, { target := 27, numerator := 71402181220989035631083520 }, { target := 28, numerator := 125350495921291862552346624 }, { target := 29, numerator := 4760145414732602375405568 }, { target := 30, numerator := 79335756912210039590092800 }, { target := 31, numerator := 4760145414732602375405568 }, { target := 32, numerator := 125350495921291862552346624 }, { target := 33, numerator := 124557138352169762156445696 }, { target := 34, numerator := 79335756912210039590092800 }, { target := 35, numerator := 1922305389982849259267948544 }, { target := 36, numerator := 122970423213925561364643840 }, { target := 37, numerator := 71402181220989035631083520 }, { target := 38, numerator := 125350495921291862552346624 }, { target := 39, numerator := 4760145414732602375405568 }, { target := 40, numerator := 122970423213925561364643840 }, { target := 41, numerator := 4760145414732602375405568 }, { target := 42, numerator := 125350495921291862552346624 }, { target := 43, numerator := 125350495921291862552346624 }, { target := 44, numerator := 4760145414732602375405568 }, { target := 61, numerator := 99368035532543074586591232 }, { target := 62, numerator := 1490520532988146118798868480 }, { target := 63, numerator := 2616691602356967630780235776 }, { target := 64, numerator := 99368035532543074586591232 }, { target := 65, numerator := 1656133925542384576443187200 }, { target := 66, numerator := 99368035532543074586591232 }, { target := 67, numerator := 2616691602356967630780235776 }, { target := 68, numerator := 2600130263101543785015803904 }, { target := 69, numerator := 1656133925542384576443187200 }, { target := 70, numerator := 40128125015891978287218425856 }, { target := 71, numerator := 2567007584590696093486940160 }, { target := 72, numerator := 1490520532988146118798868480 }, { target := 73, numerator := 2616691602356967630780235776 }, { target := 74, numerator := 99368035532543074586591232 }, { target := 75, numerator := 2567007584590696093486940160 }, { target := 76, numerator := 99368035532543074586591232 }, { target := 77, numerator := 2616691602356967630780235776 }, { target := 78, numerator := 2616691602356967630780235776 }, { target := 79, numerator := 99368035532543074586591232 }, { target := 96, numerator := 5156824199293652573356032 }, { target := 97, numerator := 77352362989404788600340480 }, { target := 98, numerator := 135796370581399517765042176 }, { target := 99, numerator := 5156824199293652573356032 }, { target := 100, numerator := 85947069988227542889267200 }, { target := 101, numerator := 5156824199293652573356032 }, { target := 102, numerator := 135796370581399517765042176 }, { target := 103, numerator := 134936899881517242336149504 }, { target := 104, numerator := 85947069988227542889267200 }, { target := 105, numerator := 2082497505814753364206944256 }, { target := 106, numerator := 133217958481752691478364160 }, { target := 107, numerator := 77352362989404788600340480 }, { target := 108, numerator := 135796370581399517765042176 }, { target := 109, numerator := 5156824199293652573356032 }, { target := 110, numerator := 133217958481752691478364160 }, { target := 111, numerator := 5156824199293652573356032 }, { target := 112, numerator := 135796370581399517765042176 }, { target := 113, numerator := 135796370581399517765042176 }, { target := 114, numerator := 5156824199293652573356032 }]

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
  [{ target := 157, numerator := 106904932439203028347650048 }, { target := 158, numerator := 1603573986588045425214750720 }, { target := 159, numerator := 2815163220899013079821451264 }, { target := 160, numerator := 106904932439203028347650048 }, { target := 161, numerator := 1781748873986717139127500800 }, { target := 162, numerator := 106904932439203028347650048 }, { target := 163, numerator := 2815163220899013079821451264 }, { target := 164, numerator := 2797345732159145908430176256 }, { target := 165, numerator := 1781748873986717139127500800 }, { target := 166, numerator := 43171775216698156281059344384 }, { target := 167, numerator := 2761710754679411565647626240 }, { target := 168, numerator := 1603573986588045425214750720 }, { target := 169, numerator := 2815163220899013079821451264 }, { target := 170, numerator := 106904932439203028347650048 }, { target := 171, numerator := 2761710754679411565647626240 }, { target := 172, numerator := 106904932439203028347650048 }, { target := 173, numerator := 2815163220899013079821451264 }, { target := 174, numerator := 2815163220899013079821451264 }, { target := 175, numerator := 106904932439203028347650048 }, { target := 192, numerator := 160059889570383754873012224 }, { target := 193, numerator := 2400898343555756323095183360 }, { target := 194, numerator := 4214910425353438878322655232 }, { target := 195, numerator := 160059889570383754873012224 }, { target := 196, numerator := 2667664826173062581216870400 }, { target := 197, numerator := 160059889570383754873012224 }, { target := 198, numerator := 4214910425353438878322655232 }, { target := 199, numerator := 4188233777091708252510486528 }, { target := 200, numerator := 2667664826173062581216870400 }, { target := 201, numerator := 64637518738173306342884769792 }, { target := 202, numerator := 4134880480568247000886149120 }, { target := 203, numerator := 2400898343555756323095183360 }, { target := 204, numerator := 4214910425353438878322655232 }, { target := 205, numerator := 160059889570383754873012224 }, { target := 206, numerator := 4134880480568247000886149120 }, { target := 207, numerator := 160059889570383754873012224 }, { target := 208, numerator := 4214910425353438878322655232 }, { target := 209, numerator := 4214910425353438878322655232 }, { target := 210, numerator := 160059889570383754873012224 }, { target := 267, numerator := 4958484807013127474380800 }, { target := 268, numerator := 74377272105196912115712000 }, { target := 269, numerator := 130573433251345690158694400 }, { target := 270, numerator := 4958484807013127474380800 }, { target := 271, numerator := 82641413450218791239680000 }, { target := 272, numerator := 4958484807013127474380800 }, { target := 273, numerator := 130573433251345690158694400 }, { target := 274, numerator := 129747019116843502246297600 }, { target := 275, numerator := 82641413450218791239680000 }, { target := 276, numerator := 2002401447898801311737446400 }, { target := 277, numerator := 128094190847839126421504000 }, { target := 278, numerator := 74377272105196912115712000 }, { target := 279, numerator := 130573433251345690158694400 }, { target := 280, numerator := 4958484807013127474380800 }, { target := 281, numerator := 128094190847839126421504000 }, { target := 282, numerator := 4958484807013127474380800 }, { target := 283, numerator := 130573433251345690158694400 }, { target := 284, numerator := 130573433251345690158694400 }, { target := 285, numerator := 4958484807013127474380800 }]

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
  [{ target := 373, numerator := 160059889570383754873012224 }, { target := 374, numerator := 2400898343555756323095183360 }, { target := 375, numerator := 4214910425353438878322655232 }, { target := 376, numerator := 160059889570383754873012224 }, { target := 377, numerator := 2667664826173062581216870400 }, { target := 378, numerator := 160059889570383754873012224 }, { target := 379, numerator := 4214910425353438878322655232 }, { target := 380, numerator := 4188233777091708252510486528 }, { target := 381, numerator := 2667664826173062581216870400 }, { target := 382, numerator := 64637518738173306342884769792 }, { target := 383, numerator := 4134880480568247000886149120 }, { target := 384, numerator := 2400898343555756323095183360 }, { target := 385, numerator := 4214910425353438878322655232 }, { target := 386, numerator := 160059889570383754873012224 }, { target := 387, numerator := 4134880480568247000886149120 }, { target := 388, numerator := 160059889570383754873012224 }, { target := 389, numerator := 4214910425353438878322655232 }, { target := 390, numerator := 4214910425353438878322655232 }, { target := 391, numerator := 160059889570383754873012224 }, { target := 408, numerator := 166803428907921608238170112 }, { target := 409, numerator := 2502051433618824123572551680 }, { target := 410, numerator := 4392490294575269016938479616 }, { target := 411, numerator := 166803428907921608238170112 }, { target := 412, numerator := 2780057148465360137302835200 }, { target := 413, numerator := 166803428907921608238170112 }, { target := 414, numerator := 4392490294575269016938479616 }, { target := 415, numerator := 4364689723090615415565451264 }, { target := 416, numerator := 2780057148465360137302835200 }, { target := 417, numerator := 67360784707315676126847696896 }, { target := 418, numerator := 4309088580121308212819394560 }, { target := 419, numerator := 2502051433618824123572551680 }, { target := 420, numerator := 4392490294575269016938479616 }, { target := 421, numerator := 166803428907921608238170112 }, { target := 422, numerator := 4309088580121308212819394560 }, { target := 423, numerator := 166803428907921608238170112 }, { target := 424, numerator := 4392490294575269016938479616 }, { target := 425, numerator := 4392490294575269016938479616 }, { target := 426, numerator := 166803428907921608238170112 }, { target := 483, numerator := 99368035532543074586591232 }, { target := 484, numerator := 1490520532988146118798868480 }, { target := 485, numerator := 2616691602356967630780235776 }, { target := 486, numerator := 99368035532543074586591232 }, { target := 487, numerator := 1656133925542384576443187200 }, { target := 488, numerator := 99368035532543074586591232 }, { target := 489, numerator := 2616691602356967630780235776 }, { target := 490, numerator := 2600130263101543785015803904 }, { target := 491, numerator := 1656133925542384576443187200 }, { target := 492, numerator := 40128125015891978287218425856 }, { target := 493, numerator := 2567007584590696093486940160 }, { target := 494, numerator := 1490520532988146118798868480 }, { target := 495, numerator := 2616691602356967630780235776 }, { target := 496, numerator := 99368035532543074586591232 }, { target := 497, numerator := 2567007584590696093486940160 }, { target := 498, numerator := 99368035532543074586591232 }, { target := 499, numerator := 2616691602356967630780235776 }, { target := 500, numerator := 2616691602356967630780235776 }, { target := 501, numerator := 99368035532543074586591232 }]

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
  [{ target := 80, numerator := 2990238546854918057443196928 }, { target := 82, numerator := 116635403416137958520172576768 }, { target := 85, numerator := 116635360634679687073901838336 }, { target := 92, numerator := 2990252807341008539533443072 }, { target := 115, numerator := 3376075778707165548726190080 }, { target := 117, numerator := 131685132889188017684065812480 }, { target := 120, numerator := 131685084587541582180211752960 }, { target := 127, numerator := 3376091879255977383344209920 }, { target := 176, numerator := 2893779238891856184622448640 }, { target := 178, numerator := 112872971047875443729199267840 }, { target := 181, numerator := 112872929646464213297324359680 }, { target := 188, numerator := 2893793039362266328580751360 }, { target := 211, numerator := 38101426645409439764195573760 }, { target := 213, numerator := 1486160785463693342434457026560 }, { target := 216, numerator := 1486160240345112141748104069120 }, { target := 223, numerator := 38101608351603173326313226240 }, { target := 237, numerator := 3376075778707165548726190080 }, { target := 239, numerator := 131685132889188017684065812480 }, { target := 242, numerator := 131685084587541582180211752960 }, { target := 249, numerator := 3376091879255977383344209920 }, { target := 286, numerator := 2893779238891856184622448640 }, { target := 288, numerator := 112872971047875443729199267840 }, { target := 291, numerator := 112872929646464213297324359680 }, { target := 298, numerator := 2893793039362266328580751360 }, { target := 312, numerator := 3376075778707165548726190080 }, { target := 314, numerator := 131685132889188017684065812480 }, { target := 317, numerator := 131685084587541582180211752960 }, { target := 324, numerator := 3376091879255977383344209920 }, { target := 392, numerator := 3376075778707165548726190080 }, { target := 394, numerator := 131685132889188017684065812480 }, { target := 397, numerator := 131685084587541582180211752960 }, { target := 404, numerator := 3376091879255977383344209920 }, { target := 427, numerator := 139962455854402777462905765888 }, { target := 429, numerator := 5459289366348908961702271254528 }, { target := 432, numerator := 5459287363900652449813921529856 }, { target := 439, numerator := 139963123337154948092355674112 }, { target := 453, numerator := 3472535086670227421546938368 }, { target := 455, numerator := 135447565257450532475039121408 }, { target := 458, numerator := 135447515575757055956789231616 }, { target := 465, numerator := 3472551647234719594296901632 }, { target := 502, numerator := 38101426645409439764195573760 }, { target := 504, numerator := 1486160785463693342434457026560 }, { target := 507, numerator := 1486160240345112141748104069120 }, { target := 514, numerator := 38101608351603173326313226240 }, { target := 623, numerator := 4958484807013127474380800 }, { target := 624, numerator := 74377272105196912115712000 }, { target := 625, numerator := 130573433251345690158694400 }, { target := 626, numerator := 4958484807013127474380800 }, { target := 627, numerator := 82641413450218791239680000 }, { target := 628, numerator := 4958484807013127474380800 }, { target := 629, numerator := 130573433251345690158694400 }, { target := 630, numerator := 129747019116843502246297600 }, { target := 631, numerator := 82641413450218791239680000 }, { target := 632, numerator := 2002401447898801311737446400 }, { target := 633, numerator := 128094190847839126421504000 }, { target := 634, numerator := 74377272105196912115712000 }, { target := 635, numerator := 130573433251345690158694400 }, { target := 636, numerator := 4958484807013127474380800 }, { target := 637, numerator := 128094190847839126421504000 }, { target := 638, numerator := 4958484807013127474380800 }, { target := 639, numerator := 130573433251345690158694400 }, { target := 640, numerator := 130573433251345690158694400 }, { target := 641, numerator := 4958484807013127474380800 }]

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
    Slot2.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 28822567246255724898570731520 }, { target := 134, numerator := 103673917261499318854546882560 }, { target := 136, numerator := 28822576861621073319674511360 }, { target := 227, numerator := 417927225070708011029275607040 }, { target := 230, numerator := 1503271800291740123390929797120 }, { target := 232, numerator := 417927364493505563135280414720 }, { target := 253, numerator := 739779225987230272396648775680 }, { target := 256, numerator := 2660963876378482517266703319040 }, { target := 258, numerator := 739779472781607548538312458240 }, { target := 302, numerator := 24018806038546437415475609600 }, { target := 305, numerator := 86394931051249432378789068800 }, { target := 307, numerator := 24018814051350894433062092800 }, { target := 328, numerator := 461161075940091598377131704320 }, { target := 331, numerator := 1658782676183989101672750120960 }, { target := 333, numerator := 461161229785937173114792181760 }, { target := 342, numerator := 24018806038546437415475609600 }, { target := 345, numerator := 86394931051249432378789068800 }, { target := 347, numerator := 24018814051350894433062092800 }, { target := 443, numerator := 734975464779520984913553653760 }, { target := 446, numerator := 2643684890168232630790945505280 }, { target := 448, numerator := 734975709971337369651700039680 }, { target := 469, numerator := 768601793233485997295219507200 }, { target := 472, numerator := 2764637793639981836121250201600 }, { target := 474, numerator := 768602049643228621857986969600 }, { target := 518, numerator := 461161075940091598377131704320 }, { target := 521, numerator := 1658782676183989101672750120960 }, { target := 523, numerator := 461161229785937173114792181760 }, { target := 528, numerator := 139962455854402777462905765888 }, { target := 530, numerator := 5459289366348908961702271254528 }, { target := 533, numerator := 5459287363900652449813921529856 }, { target := 540, numerator := 139963123337154948092355674112 }, { target := 544, numerator := 11774018720095463621066143825920 }, { target := 547, numerator := 42350795201322471752082401525760 }, { target := 549, numerator := 11774022647972208451087037890560 }, { target := 558, numerator := 754190509610358134845934141440 }, { target := 561, numerator := 2712800835009232176693976760320 }, { target := 563, numerator := 754190761212418085198149713920 }, { target := 573, numerator := 2990238546854918057443196928 }, { target := 575, numerator := 116635403416137958520172576768 }, { target := 578, numerator := 116635360634679687073901838336 }, { target := 585, numerator := 2990252807341008539533443072 }, { target := 589, numerator := 417927225070708011029275607040 }, { target := 592, numerator := 1503271800291740123390929797120 }, { target := 594, numerator := 417927364493505563135280414720 }, { target := 603, numerator := 734975464779520984913553653760 }, { target := 606, numerator := 2643684890168232630790945505280 }, { target := 608, numerator := 734975709971337369651700039680 }, { target := 642, numerator := 3376075778707165548726190080 }, { target := 644, numerator := 131685132889188017684065812480 }, { target := 647, numerator := 131685084587541582180211752960 }, { target := 654, numerator := 3376091879255977383344209920 }, { target := 658, numerator := 24018806038546437415475609600 }, { target := 661, numerator := 86394931051249432378789068800 }, { target := 663, numerator := 24018814051350894433062092800 }, { target := 668, numerator := 3472535086670227421546938368 }, { target := 670, numerator := 135447565257450532475039121408 }, { target := 673, numerator := 135447515575757055956789231616 }, { target := 680, numerator := 3472551647234719594296901632 }, { target := 713, numerator := 3376075778707165548726190080 }, { target := 715, numerator := 131685132889188017684065812480 }, { target := 718, numerator := 131685084587541582180211752960 }, { target := 725, numerator := 3376091879255977383344209920 }]

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
  [{ target := 263, numerator := 107275254317529063545873891328 }, { target := 265, numerator := 107275228741118405347580575744 }, { target := 338, numerator := 79885827683266323917140131840 }, { target := 340, numerator := 79885808637003067812028088320 }, { target := 352, numerator := 84450732122310113855262425088 }, { target := 354, numerator := 84450711987688957401286836224 }, { target := 356, numerator := 3597763239173136423925579776 }, { target := 479, numerator := 109557706537050958514935037952 }, { target := 481, numerator := 109557680416461350142209949696 }, { target := 554, numerator := 1467616777152578465106317279232 }, { target := 556, numerator := 1467616427245513502946687451136 }, { target := 568, numerator := 2654491931303963849018113523712 }, { target := 570, numerator := 2654491298423844796153961906176 }, { target := 572, numerator := 88203227799083344586562600960 }, { target := 599, numerator := 79885827683266323917140131840 }, { target := 601, numerator := 79885808637003067812028088320 }, { target := 613, numerator := 1467616777152578465106317279232 }, { target := 615, numerator := 1467616427245513502946687451136 }, { target := 617, numerator := 65223965819848473233747607552 }, { target := 618, numerator := 86733184341832008824323571712 }, { target := 620, numerator := 86733163663031902195916210176 }, { target := 622, numerator := 72767662934243759283914145792 }, { target := 684, numerator := 754190509610358134845934141440 }, { target := 687, numerator := 2712800835009232176693976760320 }, { target := 689, numerator := 754190761212418085198149713920 }, { target := 694, numerator := 86733184341832008824323571712 }, { target := 696, numerator := 86733163663031902195916210176 }, { target := 698, numerator := 24018806038546437415475609600 }, { target := 701, numerator := 86394931051249432378789068800 }, { target := 703, numerator := 24018814051350894433062092800 }, { target := 708, numerator := 84450732122310113855262425088 }, { target := 710, numerator := 84450711987688957401286836224 }, { target := 712, numerator := 3597763239173136423925579776 }, { target := 729, numerator := 734975464779520984913553653760 }, { target := 732, numerator := 2643684890168232630790945505280 }, { target := 734, numerator := 734975709971337369651700039680 }, { target := 739, numerator := 84450732122310113855262425088 }, { target := 741, numerator := 84450711987688957401286836224 }, { target := 743, numerator := 768601793233485997295219507200 }, { target := 746, numerator := 2764637793639981836121250201600 }, { target := 748, numerator := 768602049643228621857986969600 }, { target := 753, numerator := 2654491931303963849018113523712 }, { target := 755, numerator := 2654491298423844796153961906176 }, { target := 757, numerator := 72651606055560754883142352896 }, { target := 758, numerator := 84450732122310113855262425088 }, { target := 760, numerator := 84450711987688957401286836224 }, { target := 762, numerator := 73928231721073803291632074752 }, { target := 763, numerator := 28822567246255724898570731520 }, { target := 766, numerator := 103673917261499318854546882560 }, { target := 768, numerator := 28822576861621073319674511360 }, { target := 773, numerator := 107275254317529063545873891328 }, { target := 775, numerator := 107275228741118405347580575744 }, { target := 777, numerator := 3597763239173136423925579776 }, { target := 778, numerator := 109557706537050958514935037952 }, { target := 780, numerator := 109557680416461350142209949696 }, { target := 782, numerator := 88203227799083344586562600960 }, { target := 783, numerator := 3597763239173136423925579776 }]

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
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 1392682544196052809261514752 }, { target := 11, numerator := 1044511908147039606946136064 }, { target := 12, numerator := 1102540347488541807332032512 }, { target := 13, numerator := 1421696763866803909454462976 }, { target := 14, numerator := 19033328104012721726574034944 }, { target := 15, numerator := 33279309962351511921311612928 }, { target := 16, numerator := 1015497688476288506753187840 }, { target := 17, numerator := 19033328104012721726574034944 }, { target := 18, numerator := 1073526127817790707139084288 }, { target := 19, numerator := 1102540347488541807332032512 }, { target := 20, numerator := 1102540347488541807332032512 }, { target := 21, numerator := 1073526127817790707139084288 }, { target := 22, numerator := 33279309962351511921311612928 }, { target := 23, numerator := 1073526127817790707139084288 }, { target := 24, numerator := 1392682544196052809261514752 }, { target := 25, numerator := 1421696763866803909454462976 }, { target := 26, numerator := 4676711381096635672396038144 }, { target := 27, numerator := 552757259666716463135346130944 }, { target := 29, numerator := 5245556209461214954496861405184 }, { target := 37, numerator := 552757638777561234263399989248 }, { target := 44, numerator := 4676711381096635672396038144 }, { target := 80, numerator := 83324008011007819288034672640 }, { target := 82, numerator := 3260881724696538618404716675072 }, { target := 85, numerator := 3260881724696538618404716675072 }, { target := 92, numerator := 83324008011007819288034672640 }, { target := 141, numerator := 1392682544196052809261514752 }, { target := 142, numerator := 1044511908147039606946136064 }, { target := 143, numerator := 1102540347488541807332032512 }, { target := 144, numerator := 1421696763866803909454462976 }, { target := 145, numerator := 19033328104012721726574034944 }, { target := 146, numerator := 33279309962351511921311612928 }, { target := 147, numerator := 1015497688476288506753187840 }, { target := 148, numerator := 19033328104012721726574034944 }, { target := 149, numerator := 1073526127817790707139084288 }, { target := 150, numerator := 1102540347488541807332032512 }, { target := 151, numerator := 1102540347488541807332032512 }, { target := 152, numerator := 1073526127817790707139084288 }, { target := 153, numerator := 33279309962351511921311612928 }, { target := 154, numerator := 1073526127817790707139084288 }, { target := 155, numerator := 1392682544196052809261514752 }, { target := 156, numerator := 1421696763866803909454462976 }, { target := 157, numerator := 17036140250429309686942531584 }, { target := 158, numerator := 2013562401603027640946087952384 }, { target := 160, numerator := 19108305814445353520865711489024 }, { target := 168, numerator := 2013563782613099822310362185728 }, { target := 175, numerator := 17036140250429309686942531584 }, { target := 176, numerator := 3331278380434638718589070213120 }, { target := 178, numerator := 130369446332933400283688443314176 }, { target := 181, numerator := 130369446332933400283688443314176 }, { target := 188, numerator := 3331278380434638718589070213120 }, { target := 267, numerator := 4676714526978068980999127040 }, { target := 268, numerator := 552757631489704586963362775040 }, { target := 270, numerator := 5245559737987254303793285693440 }, { target := 278, numerator := 552758010600804374420316487680 }, { target := 285, numerator := 4676714526978068980999127040 }, { target := 286, numerator := 3331277566330086117401784483840 }, { target := 288, numerator := 130369414472984257909800495480832 }, { target := 291, numerator := 130369414472984257909800495480832 }, { target := 298, numerator := 3331277566330086117401784483840 }, { target := 573, numerator := 83324008011007819288034672640 }, { target := 575, numerator := 3260881724696538618404716675072 }, { target := 578, numerator := 3260881724696538618404716675072 }, { target := 585, numerator := 83324008011007819288034672640 }]

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
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left7.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 10667621369186948360647475200 }, { target := 11, numerator := 1871000565407367260561578393600 }, { target := 16, numerator := 1871000789719694976501363507200 }, { target := 24, numerator := 10667397056859232420862361600 }, { target := 26, numerator := 13841295891968029790379704320 }, { target := 27, numerator := 4458577046132633751457407959040 }, { target := 29, numerator := 47418841843687867557775264448512 }, { target := 37, numerator := 4458590484283985176729049104384 }, { target := 44, numerator := 13841295891968029790379704320 }, { target := 80, numerator := 202950828432516782520822398976 }, { target := 82, numerator := 7942703485088528003407118598144 }, { target := 85, numerator := 7942706398202560737471287525376 }, { target := 92, numerator := 202953741546549516584991326208 }, { target := 131, numerator := 39648116051143721313378500608 }, { target := 134, numerator := 147282870708665063753992110080 }, { target := 136, numerator := 39639770165403215795863945216 }, { target := 141, numerator := 10667628999267064794987888640 }, { target := 142, numerator := 1871001903651734761976123883520 }, { target := 147, numerator := 1871002127964222918652634071040 }, { target := 155, numerator := 10667404686778908118477701120 }, { target := 157, numerator := 49612669549196644244195901440 }, { target := 158, numerator := 15981300549883697680155861319680 }, { target := 160, numerator := 169967851938031427412717945749504 }, { target := 168, numerator := 15981348717524036706024059568128 }, { target := 175, numerator := 49612669549196644244195901440 }, { target := 176, numerator := 7942703485088528003407118598144 }, { target := 178, numerator := 310846420974400531785022634459136 }, { target := 181, numerator := 310846534982316434186814036639744 }, { target := 188, numerator := 7942817493004430405198520778752 }, { target := 227, numerator := 6497562620374738536372329512960 }, { target := 230, numerator := 24136825923926889673826867609600 }, { target := 232, numerator := 6496194890438933354687412305920 }, { target := 263, numerator := 37460854764004303458241871872 }, { target := 265, numerator := 37460863695369132923802353664 }, { target := 267, numerator := 13845318148972659753562931200 }, { target := 268, numerator := 4459872701026110598384346726400 }, { target := 270, numerator := 47432621678339613796683659345920 }, { target := 278, numerator := 4459886143082565911646243389440 }, { target := 285, numerator := 13845318148972659753562931200 }, { target := 286, numerator := 7942706398202560737471287525376 }, { target := 288, numerator := 310846534982316434186814036639744 }, { target := 291, numerator := 310846648990274150822295713611776 }, { target := 298, numerator := 7942820406160277372952964497408 }, { target := 302, numerator := 66894922958875244323093935554560 }, { target := 305, numerator := 248497968390453204813669308825600 }, { target := 307, numerator := 66880841649616702971298573189120 }, { target := 338, numerator := 7429792572039327493805152665600 }, { target := 340, numerator := 7429794343440126706195837747200 }, { target := 356, numerator := 5035312987322933732362420224 }, { target := 589, numerator := 6497562620374738536372329512960 }, { target := 592, numerator := 24136825923926889673826867609600 }, { target := 594, numerator := 6496194890438933354687412305920 }, { target := 599, numerator := 7429792572039327493805152665600 }, { target := 601, numerator := 7429794343440126706195837747200 }, { target := 617, numerator := 227586986580493134164995866624 }, { target := 763, numerator := 39648116051143721313378500608 }, { target := 766, numerator := 147282870708665063753992110080 }, { target := 768, numerator := 39639770165403215795863945216 }, { target := 773, numerator := 37460854764004303458241871872 }, { target := 775, numerator := 37460863695369132923802353664 }, { target := 777, numerator := 5062187974976944883273564160 }]

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
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left6.expected,
    Slot16.Left14.expected,
    Slot18.Left0.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 5035312987322933732362420224 }, { target := 2, numerator := 227586986580493134164995866624 }, { target := 7, numerator := 5062187974976944883273564160 }, { target := 10, numerator := 38057048739028244627338559488 }, { target := 11, numerator := 7548038607668600610417436262400 }, { target := 16, numerator := 7548038607668600610417436262400 }, { target := 24, numerator := 38057048739028244627338559488 }, { target := 26, numerator := 39634368438088539717916164096 }, { target := 27, numerator := 6495309651366286823981076971520 }, { target := 29, numerator := 66871727770609337511608812830720 }, { target := 37, numerator := 6495309651366286823981076971520 }, { target := 44, numerator := 39634368438088539717916164096 }, { target := 80, numerator := 83480564175792195881580625920 }, { target := 82, numerator := 3337537466855458245015093903360 }, { target := 85, numerator := 3337536651221297436888158699520 }, { target := 92, numerator := 83480564175792195881580625920 }, { target := 131, numerator := 13855231251537088969630023680 }, { target := 134, numerator := 49662619380104468703540674560 }, { target := 136, numerator := 13859257558133467868089548800 }, { target := 141, numerator := 38057057812536811431873478656 }, { target := 142, numerator := 7548040407261454982687018188800 }, { target := 147, numerator := 7548040407261454982687018188800 }, { target := 155, numerator := 38057057812536811431873478656 }, { target := 157, numerator := 147231801752108661166005288960 }, { target := 158, numerator := 24128456705506665370888647475200 }, { target := 160, numerator := 248411804046351105921570255667200 }, { target := 168, numerator := 24128456705506665370888647475200 }, { target := 175, numerator := 147231801752108661166005288960 }, { target := 176, numerator := 3267008543950918586902947823616 }, { target := 178, numerator := 130614395429960157648002354249728 }, { target := 181, numerator := 130614363510149859203748668112896 }, { target := 188, numerator := 3267008543950918586902947823616 }, { target := 227, numerator := 4463065923098284527950191656960 }, { target := 230, numerator := 15997390457308700144470138552320 }, { target := 232, numerator := 4464362882451759841372903833600 }, { target := 263, numerator := 10892202871696147273503211520 }, { target := 265, numerator := 10892210662409529316987633664 }, { target := 267, numerator := 39626025446205780561538056192 }, { target := 268, numerator := 6493942395678032198877881303040 }, { target := 270, numerator := 66857651343912952380809218621440 }, { target := 278, numerator := 6493942395678032198877881303040 }, { target := 285, numerator := 39626025446205780561538056192 }, { target := 302, numerator := 47466582937917606160904159756288 }, { target := 305, numerator := 170138974869758617372358235652096 }, { target := 307, numerator := 47480376646049998507276847022080 }, { target := 338, numerator := 1910390050994890781836558991360 }, { target := 340, numerator := 1910391417412823914859831754752 }, { target := 573, numerator := 202953741546549516584991326208 }, { target := 575, numerator := 7942817493004430405198520778752 }, { target := 578, numerator := 7942820406160277372952964497408 }, { target := 585, numerator := 202956654702396484339435044864 }, { target := 589, numerator := 4463079374779111262988026249216 }, { target := 592, numerator := 15997438673444020634245578883072 }, { target := 594, numerator := 4464376338041622106875688386560 }, { target := 599, numerator := 1910390280029583291796129054720 }, { target := 601, numerator := 1910391646447680243255847419904 }, { target := 763, numerator := 13855231251537088969630023680 }, { target := 766, numerator := 49662619380104468703540674560 }, { target := 768, numerator := 13859257558133467868089548800 }, { target := 773, numerator := 10891973837003637313933148160 }, { target := 775, numerator := 10891981627553200920971968512 }]

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
    Slot21.Left5.expected,
    Slot21.Left12.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected,
    Slot22.Left3.expected,
    Slot22.Left11.expected,
    Slot22.Left18.expected,
    Slot23.Left0.expected,
    Slot23.Left1.expected,
    Slot23.Left2.expected,
    Slot23.Left3.expected,
    Slot23.Left4.expected,
    Slot23.Left5.expected,
    Slot23.Left6.expected,
    Slot23.Left7.expected,
    Slot23.Left8.expected,
    Slot23.Left9.expected,
    Slot23.Left10.expected,
    Slot23.Left11.expected,
    Slot23.Left12.expected,
    Slot23.Left13.expected,
    Slot23.Left14.expected,
    Slot23.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 4728330712013817081583632384 }, { target := 134, numerator := 17224177118535593458321588224 }, { target := 136, numerator := 4728333892618003517213245440 }, { target := 227, numerator := 558858333172971611735074013184 }, { target := 230, numerator := 2035787152172597482457634177024 }, { target := 232, numerator := 558858709099966226996070973440 }, { target := 263, numerator := 1392682544196052809261514752 }, { target := 265, numerator := 1392682544196052809261514752 }, { target := 286, numerator := 3267008543950918586902947823616 }, { target := 288, numerator := 130614395429960157648002354249728 }, { target := 291, numerator := 130614363510149859203748668112896 }, { target := 298, numerator := 3267008543950918586902947823616 }, { target := 302, numerator := 5303454180868071631698813517824 }, { target := 305, numerator := 19319214267143425855533103448064 }, { target := 307, numerator := 5303457748340314505821909155840 }, { target := 338, numerator := 1044511908147039606946136064 }, { target := 340, numerator := 1044511908147039606946136064 }, { target := 352, numerator := 1102540347488541807332032512 }, { target := 354, numerator := 1102540347488541807332032512 }, { target := 479, numerator := 1421696763866803909454462976 }, { target := 481, numerator := 1421696763866803909454462976 }, { target := 554, numerator := 19033328104012721726574034944 }, { target := 556, numerator := 19033328104012721726574034944 }, { target := 568, numerator := 33279309962351511921311612928 }, { target := 570, numerator := 33279309962351511921311612928 }, { target := 573, numerator := 83480564175792195881580625920 }, { target := 575, numerator := 3337537466855458245015093903360 }, { target := 578, numerator := 3337536651221297436888158699520 }, { target := 585, numerator := 83480564175792195881580625920 }, { target := 589, numerator := 558858716468262793140479459328 }, { target := 592, numerator := 2035788548425606442865664196608 }, { target := 594, numerator := 558859092395515239480143380480 }, { target := 599, numerator := 1015497688476288506753187840 }, { target := 601, numerator := 1015497688476288506753187840 }, { target := 613, numerator := 19033328104012721726574034944 }, { target := 615, numerator := 19033328104012721726574034944 }, { target := 618, numerator := 1073526127817790707139084288 }, { target := 620, numerator := 1073526127817790707139084288 }, { target := 694, numerator := 1102540347488541807332032512 }, { target := 696, numerator := 1102540347488541807332032512 }, { target := 708, numerator := 1102540347488541807332032512 }, { target := 710, numerator := 1102540347488541807332032512 }, { target := 739, numerator := 1073526127817790707139084288 }, { target := 741, numerator := 1073526127817790707139084288 }, { target := 753, numerator := 33279309962351511921311612928 }, { target := 755, numerator := 33279309962351511921311612928 }, { target := 758, numerator := 1073526127817790707139084288 }, { target := 760, numerator := 1073526127817790707139084288 }, { target := 763, numerator := 4728330712013817081583632384 }, { target := 766, numerator := 17224177118535593458321588224 }, { target := 768, numerator := 4728333892618003517213245440 }, { target := 773, numerator := 1392682544196052809261514752 }, { target := 775, numerator := 1392682544196052809261514752 }, { target := 778, numerator := 1421696763866803909454462976 }, { target := 780, numerator := 1421696763866803909454462976 }]

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
    Slot24.Left0.expected,
    Slot25.Left0.expected,
    Slot25.Left2.expected,
    Slot26.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 3597763239173136423925579776 }, { target := 1, numerator := 88203227799083344586562600960 }, { target := 2, numerator := 65223965819848473233747607552 }, { target := 3, numerator := 72767662934243759283914145792 }, { target := 4, numerator := 3597763239173136423925579776 }, { target := 5, numerator := 72651606055560754883142352896 }, { target := 6, numerator := 73928231721073803291632074752 }, { target := 7, numerator := 3597763239173136423925579776 }, { target := 8, numerator := 88203227799083344586562600960 }, { target := 9, numerator := 3597763239173136423925579776 }, { target := 10, numerator := 106366141992804240973451231232 }, { target := 11, numerator := 79208829143577626256825384960 }, { target := 12, numerator := 83735047951782062042929692672 }, { target := 13, numerator := 108629251396906458866503385088 }, { target := 14, numerator := 1455179346837726105232534929408 }, { target := 15, numerator := 2631996236970879409619654934528 }, { target := 16, numerator := 79208829143577626256825384960 }, { target := 17, numerator := 1455179346837726105232534929408 }, { target := 18, numerator := 85998157355884279935981846528 }, { target := 19, numerator := 85998157355884279935981846528 }, { target := 20, numerator := 83735047951782062042929692672 }, { target := 21, numerator := 83735047951782062042929692672 }, { target := 22, numerator := 2631996236970879409619654934528 }, { target := 23, numerator := 83735047951782062042929692672 }, { target := 24, numerator := 106366141992804240973451231232 }, { target := 25, numerator := 108629251396906458866503385088 }, { target := 26, numerator := 28718888946808761859367239680 }, { target := 27, numerator := 416423889728727046960824975360 }, { target := 28, numerator := 737118149634758221057092485120 }, { target := 29, numerator := 23932407455673968216139366400 }, { target := 30, numerator := 459502223148940189749875834880 }, { target := 31, numerator := 23932407455673968216139366400 }, { target := 32, numerator := 732331668143623427413864611840 }, { target := 33, numerator := 765837038581566982916459724800 }, { target := 34, numerator := 459502223148940189749875834880 }, { target := 35, numerator := 11731666134771379219551517409280 }, { target := 36, numerator := 751477594108162601986776104960 }, { target := 37, numerator := 416423889728727046960824975360 }, { target := 38, numerator := 732331668143623427413864611840 }, { target := 39, numerator := 23932407455673968216139366400 }, { target := 40, numerator := 751477594108162601986776104960 }, { target := 41, numerator := 23932407455673968216139366400 }, { target := 42, numerator := 732331668143623427413864611840 }, { target := 43, numerator := 765837038581566982916459724800 }, { target := 44, numerator := 28718888946808761859367239680 }, { target := 141, numerator := 106366116633142825641245147136 }, { target := 142, numerator := 79208810258723380796671918080 }, { target := 143, numerator := 83735027987793288270767456256 }, { target := 144, numerator := 108629225497677779378292916224 }, { target := 145, numerator := 1455178999895975252921715523584 }, { target := 146, numerator := 2631995609454151196186555449344 }, { target := 147, numerator := 79208810258723380796671918080 }, { target := 148, numerator := 1455178999895975252921715523584 }, { target := 149, numerator := 85998136852328242007815225344 }, { target := 150, numerator := 85998136852328242007815225344 }, { target := 151, numerator := 83735027987793288270767456256 }, { target := 152, numerator := 83735027987793288270767456256 }, { target := 153, numerator := 2631995609454151196186555449344 }, { target := 154, numerator := 83735027987793288270767456256 }, { target := 155, numerator := 106366116633142825641245147136 }, { target := 156, numerator := 108629225497677779378292916224 }]

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
    Slot26.Left3.expected,
    Slot26.Left5.expected,
    Slot27.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 2900306560483341574512574464 }, { target := 81, numerator := 3274539665061837261546455040 }, { target := 82, numerator := 2806748284338717652754104320 }, { target := 83, numerator := 36955519077126449094595706880 }, { target := 84, numerator := 3274539665061837261546455040 }, { target := 85, numerator := 2806748284338717652754104320 }, { target := 86, numerator := 3274539665061837261546455040 }, { target := 87, numerator := 3274539665061837261546455040 }, { target := 88, numerator := 135753058685849310471540178944 }, { target := 89, numerator := 3368097941206461183304925184 }, { target := 90, numerator := 36955519077126449094595706880 }, { target := 91, numerator := 135753058685849310471540178944 }, { target := 92, numerator := 2900306560483341574512574464 }, { target := 93, numerator := 3274539665061837261546455040 }, { target := 94, numerator := 3368097941206461183304925184 }, { target := 95, numerator := 3274539665061837261546455040 }, { target := 157, numerator := 103300989501565868067300311040 }, { target := 158, numerator := 1497864347772705086975854510080 }, { target := 159, numerator := 2651392063873523947060707983360 }, { target := 160, numerator := 86084157917971556722750259200 }, { target := 161, numerator := 1652815832025053889076804976640 }, { target := 162, numerator := 86084157917971556722750259200 }, { target := 163, numerator := 2634175232289929635716157931520 }, { target := 164, numerator := 2754693053375089815128008294400 }, { target := 165, numerator := 1652815832025053889076804976640 }, { target := 166, numerator := 42198454211389657105492177059840 }, { target := 167, numerator := 2703042558624306881094358138880 }, { target := 168, numerator := 1497864347772705086975854510080 }, { target := 169, numerator := 2634175232289929635716157931520 }, { target := 170, numerator := 86084157917971556722750259200 }, { target := 171, numerator := 2703042558624306881094358138880 }, { target := 172, numerator := 86084157917971556722750259200 }, { target := 173, numerator := 2634175232289929635716157931520 }, { target := 174, numerator := 2754693053375089815128008294400 }, { target := 175, numerator := 103300989501565868067300311040 }, { target := 267, numerator := 28718898527586465142265610240 }, { target := 268, numerator := 416424028650003744562851348480 }, { target := 269, numerator := 737118395541385938651483996160 }, { target := 270, numerator := 23932415439655387618554675200 }, { target := 271, numerator := 459502376441383442276249763840 }, { target := 272, numerator := 23932415439655387618554675200 }, { target := 273, numerator := 732331912453454861127773061120 }, { target := 274, numerator := 765837294068972403793749606400 }, { target := 275, numerator := 459502376441383442276249763840 }, { target := 276, numerator := 11731670048519071010615501783040 }, { target := 277, numerator := 751477844805179171222616801280 }, { target := 278, numerator := 416424028650003744562851348480 }, { target := 279, numerator := 732331912453454861127773061120 }, { target := 280, numerator := 23932415439655387618554675200 }, { target := 281, numerator := 751477844805179171222616801280 }, { target := 282, numerator := 23932415439655387618554675200 }, { target := 283, numerator := 732331912453454861127773061120 }, { target := 284, numerator := 765837294068972403793749606400 }, { target := 285, numerator := 28718898527586465142265610240 }]

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
    Slot27.Left2.expected,
    Slot27.Left5.expected,
    Slot27.Left12.expected,
    Slot28.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 4760145414732602375405568 }, { target := 132, numerator := 99368035532543074586591232 }, { target := 133, numerator := 5156824199293652573356032 }, { target := 134, numerator := 106904932439203028347650048 }, { target := 135, numerator := 160059889570383754873012224 }, { target := 136, numerator := 4958484807013127474380800 }, { target := 137, numerator := 160059889570383754873012224 }, { target := 138, numerator := 166803428907921608238170112 }, { target := 139, numerator := 99368035532543074586591232 }, { target := 140, numerator := 4958484807013127474380800 }, { target := 176, numerator := 113127571734449598865430544384 }, { target := 177, numerator := 127724677764701160009357066240 }, { target := 178, numerator := 109478295226886708579448913920 }, { target := 179, numerator := 1441464220487341662962744033280 }, { target := 180, numerator := 127724677764701160009357066240 }, { target := 181, numerator := 109478295226886708579448913920 }, { target := 182, numerator := 127724677764701160009357066240 }, { target := 183, numerator := 127724677764701160009357066240 }, { target := 184, numerator := 5295100212473753804959345803264 }, { target := 185, numerator := 131373954272264050295338696704 }, { target := 186, numerator := 1441464220487341662962744033280 }, { target := 187, numerator := 5295100212473753804959345803264 }, { target := 188, numerator := 113127571734449598865430544384 }, { target := 189, numerator := 127724677764701160009357066240 }, { target := 190, numerator := 131373954272264050295338696704 }, { target := 191, numerator := 127724677764701160009357066240 }, { target := 286, numerator := 113127530239651726560401031168 }, { target := 287, numerator := 127724630915735820310130196480 }, { target := 288, numerator := 109478255070630703122968739840 }, { target := 289, numerator := 1441463691763304257785755074560 }, { target := 290, numerator := 127724630915735820310130196480 }, { target := 291, numerator := 109478255070630703122968739840 }, { target := 292, numerator := 127724630915735820310130196480 }, { target := 293, numerator := 127724630915735820310130196480 }, { target := 294, numerator := 5295098270249505007714254716928 }, { target := 295, numerator := 131373906084756843747562487808 }, { target := 296, numerator := 1441463691763304257785755074560 }, { target := 297, numerator := 5295098270249505007714254716928 }, { target := 298, numerator := 113127530239651726560401031168 }, { target := 299, numerator := 127724630915735820310130196480 }, { target := 300, numerator := 131373906084756843747562487808 }, { target := 301, numerator := 127724630915735820310130196480 }, { target := 573, numerator := 2900320392082632342855745536 }, { target := 574, numerator := 3274555281383617161288744960 }, { target := 575, numerator := 2806761669757386138247495680 }, { target := 576, numerator := 36955695318472250820258693120 }, { target := 577, numerator := 3274555281383617161288744960 }, { target := 578, numerator := 2806761669757386138247495680 }, { target := 579, numerator := 3274555281383617161288744960 }, { target := 580, numerator := 3274555281383617161288744960 }, { target := 581, numerator := 135753706093932242886570541056 }, { target := 582, numerator := 3368114003708863365896994816 }, { target := 583, numerator := 36955695318472250820258693120 }, { target := 584, numerator := 135753706093932242886570541056 }, { target := 585, numerator := 2900320392082632342855745536 }, { target := 586, numerator := 3274555281383617161288744960 }, { target := 587, numerator := 3368114003708863365896994816 }, { target := 588, numerator := 3274555281383617161288744960 }]

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
    Slot28.Left1.expected,
    Slot28.Left2.expected,
    Slot28.Left3.expected,
    Slot28.Left4.expected,
    Slot28.Left5.expected,
    Slot28.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 227, numerator := 71402181220989035631083520 }, { target := 228, numerator := 1490520532988146118798868480 }, { target := 229, numerator := 77352362989404788600340480 }, { target := 230, numerator := 1603573986588045425214750720 }, { target := 231, numerator := 2400898343555756323095183360 }, { target := 232, numerator := 74377272105196912115712000 }, { target := 233, numerator := 2400898343555756323095183360 }, { target := 234, numerator := 2502051433618824123572551680 }, { target := 235, numerator := 1490520532988146118798868480 }, { target := 236, numerator := 74377272105196912115712000 }, { target := 253, numerator := 125350495921291862552346624 }, { target := 254, numerator := 2616691602356967630780235776 }, { target := 255, numerator := 135796370581399517765042176 }, { target := 256, numerator := 2815163220899013079821451264 }, { target := 257, numerator := 4214910425353438878322655232 }, { target := 258, numerator := 130573433251345690158694400 }, { target := 259, numerator := 4214910425353438878322655232 }, { target := 260, numerator := 4392490294575269016938479616 }, { target := 261, numerator := 2616691602356967630780235776 }, { target := 262, numerator := 130573433251345690158694400 }, { target := 302, numerator := 4760145414732602375405568 }, { target := 303, numerator := 99368035532543074586591232 }, { target := 304, numerator := 5156824199293652573356032 }, { target := 305, numerator := 106904932439203028347650048 }, { target := 306, numerator := 160059889570383754873012224 }, { target := 307, numerator := 4958484807013127474380800 }, { target := 308, numerator := 160059889570383754873012224 }, { target := 309, numerator := 166803428907921608238170112 }, { target := 310, numerator := 99368035532543074586591232 }, { target := 311, numerator := 4958484807013127474380800 }, { target := 328, numerator := 79335756912210039590092800 }, { target := 329, numerator := 1656133925542384576443187200 }, { target := 330, numerator := 85947069988227542889267200 }, { target := 331, numerator := 1781748873986717139127500800 }, { target := 332, numerator := 2667664826173062581216870400 }, { target := 333, numerator := 82641413450218791239680000 }, { target := 334, numerator := 2667664826173062581216870400 }, { target := 335, numerator := 2780057148465360137302835200 }, { target := 336, numerator := 1656133925542384576443187200 }, { target := 337, numerator := 82641413450218791239680000 }, { target := 342, numerator := 4760145414732602375405568 }, { target := 343, numerator := 99368035532543074586591232 }, { target := 344, numerator := 5156824199293652573356032 }, { target := 345, numerator := 106904932439203028347650048 }, { target := 346, numerator := 160059889570383754873012224 }, { target := 347, numerator := 4958484807013127474380800 }, { target := 348, numerator := 160059889570383754873012224 }, { target := 349, numerator := 166803428907921608238170112 }, { target := 350, numerator := 99368035532543074586591232 }, { target := 351, numerator := 4958484807013127474380800 }, { target := 443, numerator := 125350495921291862552346624 }, { target := 444, numerator := 2616691602356967630780235776 }, { target := 445, numerator := 135796370581399517765042176 }, { target := 446, numerator := 2815163220899013079821451264 }, { target := 447, numerator := 4214910425353438878322655232 }, { target := 448, numerator := 130573433251345690158694400 }, { target := 449, numerator := 4214910425353438878322655232 }, { target := 450, numerator := 4392490294575269016938479616 }, { target := 451, numerator := 2616691602356967630780235776 }, { target := 452, numerator := 130573433251345690158694400 }]

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
    Slot28.Left7.expected,
    Slot28.Left8.expected,
    Slot28.Left9.expected,
    Slot28.Left10.expected,
    Slot28.Left11.expected,
    Slot28.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 469, numerator := 124557138352169762156445696 }, { target := 470, numerator := 2600130263101543785015803904 }, { target := 471, numerator := 134936899881517242336149504 }, { target := 472, numerator := 2797345732159145908430176256 }, { target := 473, numerator := 4188233777091708252510486528 }, { target := 474, numerator := 129747019116843502246297600 }, { target := 475, numerator := 4188233777091708252510486528 }, { target := 476, numerator := 4364689723090615415565451264 }, { target := 477, numerator := 2600130263101543785015803904 }, { target := 478, numerator := 129747019116843502246297600 }, { target := 518, numerator := 79335756912210039590092800 }, { target := 519, numerator := 1656133925542384576443187200 }, { target := 520, numerator := 85947069988227542889267200 }, { target := 521, numerator := 1781748873986717139127500800 }, { target := 522, numerator := 2667664826173062581216870400 }, { target := 523, numerator := 82641413450218791239680000 }, { target := 524, numerator := 2667664826173062581216870400 }, { target := 525, numerator := 2780057148465360137302835200 }, { target := 526, numerator := 1656133925542384576443187200 }, { target := 527, numerator := 82641413450218791239680000 }, { target := 544, numerator := 1922305389982849259267948544 }, { target := 545, numerator := 40128125015891978287218425856 }, { target := 546, numerator := 2082497505814753364206944256 }, { target := 547, numerator := 43171775216698156281059344384 }, { target := 548, numerator := 64637518738173306342884769792 }, { target := 549, numerator := 2002401447898801311737446400 }, { target := 550, numerator := 64637518738173306342884769792 }, { target := 551, numerator := 67360784707315676126847696896 }, { target := 552, numerator := 40128125015891978287218425856 }, { target := 553, numerator := 2002401447898801311737446400 }, { target := 558, numerator := 122970423213925561364643840 }, { target := 559, numerator := 2567007584590696093486940160 }, { target := 560, numerator := 133217958481752691478364160 }, { target := 561, numerator := 2761710754679411565647626240 }, { target := 562, numerator := 4134880480568247000886149120 }, { target := 563, numerator := 128094190847839126421504000 }, { target := 564, numerator := 4134880480568247000886149120 }, { target := 565, numerator := 4309088580121308212819394560 }, { target := 566, numerator := 2567007584590696093486940160 }, { target := 567, numerator := 128094190847839126421504000 }, { target := 589, numerator := 71402181220989035631083520 }, { target := 590, numerator := 1490520532988146118798868480 }, { target := 591, numerator := 77352362989404788600340480 }, { target := 592, numerator := 1603573986588045425214750720 }, { target := 593, numerator := 2400898343555756323095183360 }, { target := 594, numerator := 74377272105196912115712000 }, { target := 595, numerator := 2400898343555756323095183360 }, { target := 596, numerator := 2502051433618824123572551680 }, { target := 597, numerator := 1490520532988146118798868480 }, { target := 598, numerator := 74377272105196912115712000 }, { target := 603, numerator := 125350495921291862552346624 }, { target := 604, numerator := 2616691602356967630780235776 }, { target := 605, numerator := 135796370581399517765042176 }, { target := 606, numerator := 2815163220899013079821451264 }, { target := 607, numerator := 4214910425353438878322655232 }, { target := 608, numerator := 130573433251345690158694400 }, { target := 609, numerator := 4214910425353438878322655232 }, { target := 610, numerator := 4392490294575269016938479616 }, { target := 611, numerator := 2616691602356967630780235776 }, { target := 612, numerator := 130573433251345690158694400 }]

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
    Slot28.Left13.expected,
    Slot28.Left14.expected,
    Slot28.Left15.expected,
    Slot28.Left16.expected,
    Slot28.Left17.expected,
    Slot28.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 658, numerator := 4760145414732602375405568 }, { target := 659, numerator := 99368035532543074586591232 }, { target := 660, numerator := 5156824199293652573356032 }, { target := 661, numerator := 106904932439203028347650048 }, { target := 662, numerator := 160059889570383754873012224 }, { target := 663, numerator := 4958484807013127474380800 }, { target := 664, numerator := 160059889570383754873012224 }, { target := 665, numerator := 166803428907921608238170112 }, { target := 666, numerator := 99368035532543074586591232 }, { target := 667, numerator := 4958484807013127474380800 }, { target := 684, numerator := 122970423213925561364643840 }, { target := 685, numerator := 2567007584590696093486940160 }, { target := 686, numerator := 133217958481752691478364160 }, { target := 687, numerator := 2761710754679411565647626240 }, { target := 688, numerator := 4134880480568247000886149120 }, { target := 689, numerator := 128094190847839126421504000 }, { target := 690, numerator := 4134880480568247000886149120 }, { target := 691, numerator := 4309088580121308212819394560 }, { target := 692, numerator := 2567007584590696093486940160 }, { target := 693, numerator := 128094190847839126421504000 }, { target := 698, numerator := 4760145414732602375405568 }, { target := 699, numerator := 99368035532543074586591232 }, { target := 700, numerator := 5156824199293652573356032 }, { target := 701, numerator := 106904932439203028347650048 }, { target := 702, numerator := 160059889570383754873012224 }, { target := 703, numerator := 4958484807013127474380800 }, { target := 704, numerator := 160059889570383754873012224 }, { target := 705, numerator := 166803428907921608238170112 }, { target := 706, numerator := 99368035532543074586591232 }, { target := 707, numerator := 4958484807013127474380800 }, { target := 729, numerator := 125350495921291862552346624 }, { target := 730, numerator := 2616691602356967630780235776 }, { target := 731, numerator := 135796370581399517765042176 }, { target := 732, numerator := 2815163220899013079821451264 }, { target := 733, numerator := 4214910425353438878322655232 }, { target := 734, numerator := 130573433251345690158694400 }, { target := 735, numerator := 4214910425353438878322655232 }, { target := 736, numerator := 4392490294575269016938479616 }, { target := 737, numerator := 2616691602356967630780235776 }, { target := 738, numerator := 130573433251345690158694400 }, { target := 743, numerator := 125350495921291862552346624 }, { target := 744, numerator := 2616691602356967630780235776 }, { target := 745, numerator := 135796370581399517765042176 }, { target := 746, numerator := 2815163220899013079821451264 }, { target := 747, numerator := 4214910425353438878322655232 }, { target := 748, numerator := 130573433251345690158694400 }, { target := 749, numerator := 4214910425353438878322655232 }, { target := 750, numerator := 4392490294575269016938479616 }, { target := 751, numerator := 2616691602356967630780235776 }, { target := 752, numerator := 130573433251345690158694400 }, { target := 763, numerator := 4760145414732602375405568 }, { target := 764, numerator := 99368035532543074586591232 }, { target := 765, numerator := 5156824199293652573356032 }, { target := 766, numerator := 106904932439203028347650048 }, { target := 767, numerator := 160059889570383754873012224 }, { target := 768, numerator := 4958484807013127474380800 }, { target := 769, numerator := 160059889570383754873012224 }, { target := 770, numerator := 166803428907921608238170112 }, { target := 771, numerator := 99368035532543074586591232 }, { target := 772, numerator := 4958484807013127474380800 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent2
