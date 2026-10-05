import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 8; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent3

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
    Slot1.Left4.expected,
    Slot1.Left5.expected,
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
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 38109058253664781665828864 }, { target := 12, numerator := 1722460103514474404080779264 }, { target := 17, numerator := 38312457818429026216181760 }, { target := 24, numerator := 43026356092847334138839040 }, { target := 26, numerator := 1944713020096987230413783040 }, { target := 31, numerator := 43256000762742448953753600 }, { target := 34, numerator := 36679907132847675616002048 }, { target := 35, numerator := 7274903449896429573006950400 }, { target := 40, numerator := 7274903449896429573006950400 }, { target := 48, numerator := 36679907132847675616002048 }, { target := 55, numerator := 36879733793869143547576320 }, { target := 57, numerator := 1666896874368846197497528320 }, { target := 62, numerator := 37076572082350670531788800 }, { target := 69, numerator := 485583161619277056709754880 }, { target := 71, numerator := 21947475512523141600384122880 }, { target := 76, numerator := 488174865750950495335219200 }, { target := 79, numerator := 531858653426291296432029696 }, { target := 80, numerator := 105486100023498228808600780800 }, { target := 85, numerator := 105486100023498228808600780800 }, { target := 93, numerator := 531858653426291296432029696 }, { target := 95, numerator := 43026356092847334138839040 }, { target := 97, numerator := 1944713020096987230413783040 }, { target := 102, numerator := 43256000762742448953753600 }, { target := 105, numerator := 941450949743090340810719232 }, { target := 106, numerator := 186722521880675025707178393600 }, { target := 111, numerator := 186722521880675025707178393600 }, { target := 119, numerator := 941450949743090340810719232 }, { target := 144, numerator := 36879733793869143547576320 }, { target := 146, numerator := 1666896874368846197497528320 }, { target := 151, numerator := 37076572082350670531788800 }, { target := 154, numerator := 30566589277373063013335040 }, { target := 155, numerator := 6062419541580357977505792000 }, { target := 160, numerator := 6062419541580357977505792000 }, { target := 168, numerator := 30566589277373063013335040 }, { target := 170, numerator := 43026356092847334138839040 }, { target := 172, numerator := 1944713020096987230413783040 }, { target := 177, numerator := 43256000762742448953753600 }, { target := 271, numerator := 43026356092847334138839040 }, { target := 273, numerator := 1944713020096987230413783040 }, { target := 278, numerator := 43256000762742448953753600 }, { target := 285, numerator := 1783749791163470909584441344 }, { target := 287, numerator := 80622245490306527752297119744 }, { target := 292, numerator := 1793270203049694098054184960 }, { target := 311, numerator := 44255680552642972257091584 }, { target := 313, numerator := 2000276249242615436997033984 }, { target := 318, numerator := 44491886498820804638146560 }, { target := 360, numerator := 485583161619277056709754880 }, { target := 362, numerator := 21947475512523141600384122880 }, { target := 367, numerator := 488174865750950495335219200 }, { target := 386, numerator := 1783749791163470909584441344 }, { target := 388, numerator := 80622245490306527752297119744 }, { target := 393, numerator := 1793270203049694098054184960 }, { target := 482, numerator := 38109058253664781665828864 }, { target := 484, numerator := 1722460103514474404080779264 }, { target := 489, numerator := 38312457818429026216181760 }, { target := 627, numerator := 43026356092847334138839040 }, { target := 629, numerator := 1944713020096987230413783040 }, { target := 634, numerator := 43256000762742448953753600 }, { target := 653, numerator := 44255680552642972257091584 }, { target := 655, numerator := 2000276249242615436997033984 }, { target := 660, numerator := 44491886498820804638146560 }, { target := 749, numerator := 43026356092847334138839040 }, { target := 751, numerator := 1944713020096987230413783040 }, { target := 756, numerator := 43256000762742448953753600 }]

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
    Slot2.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 180, numerator := 586878514125562809856032768 }, { target := 181, numerator := 116398455198342873168111206400 }, { target := 186, numerator := 116398455198342873168111206400 }, { target := 194, numerator := 586878514125562809856032768 }, { target := 215, numerator := 30566589277373063013335040 }, { target := 216, numerator := 6062419541580357977505792000 }, { target := 221, numerator := 6062419541580357977505792000 }, { target := 229, numerator := 30566589277373063013335040 }, { target := 295, numerator := 935337631887615728208052224 }, { target := 296, numerator := 185510037972358954111677235200 }, { target := 301, numerator := 185510037972358954111677235200 }, { target := 309, numerator := 935337631887615728208052224 }, { target := 321, numerator := 978130856875938016426721280 }, { target := 322, numerator := 193997425330571455280185344000 }, { target := 327, numerator := 193997425330571455280185344000 }, { target := 335, numerator := 978130856875938016426721280 }, { target := 370, numerator := 586878514125562809856032768 }, { target := 371, numerator := 116398455198342873168111206400 }, { target := 376, numerator := 116398455198342873168111206400 }, { target := 384, numerator := 586878514125562809856032768 }, { target := 396, numerator := 14983742063768275489136836608 }, { target := 397, numerator := 2971798059282691480573339238400 }, { target := 402, numerator := 2971798059282691480573339238400 }, { target := 410, numerator := 14983742063768275489136836608 }, { target := 431, numerator := 959790903309514178618720256 }, { target := 432, numerator := 190359973605623240493681868800 }, { target := 437, numerator := 190359973605623240493681868800 }, { target := 445, numerator := 959790903309514178618720256 }, { target := 492, numerator := 531858653426291296432029696 }, { target := 493, numerator := 105486100023498228808600780800 }, { target := 498, numerator := 105486100023498228808600780800 }, { target := 506, numerator := 531858653426291296432029696 }, { target := 527, numerator := 935337631887615728208052224 }, { target := 528, numerator := 185510037972358954111677235200 }, { target := 533, numerator := 185510037972358954111677235200 }, { target := 541, numerator := 935337631887615728208052224 }, { target := 637, numerator := 30566589277373063013335040 }, { target := 638, numerator := 6062419541580357977505792000 }, { target := 643, numerator := 6062419541580357977505792000 }, { target := 651, numerator := 30566589277373063013335040 }, { target := 663, numerator := 959790903309514178618720256 }, { target := 664, numerator := 190359973605623240493681868800 }, { target := 669, numerator := 190359973605623240493681868800 }, { target := 677, numerator := 959790903309514178618720256 }, { target := 698, numerator := 30566589277373063013335040 }, { target := 699, numerator := 6062419541580357977505792000 }, { target := 704, numerator := 6062419541580357977505792000 }, { target := 712, numerator := 30566589277373063013335040 }, { target := 759, numerator := 935337631887615728208052224 }, { target := 760, numerator := 185510037972358954111677235200 }, { target := 765, numerator := 185510037972358954111677235200 }, { target := 773, numerator := 935337631887615728208052224 }, { target := 794, numerator := 978130856875938016426721280 }, { target := 795, numerator := 193997425330571455280185344000 }, { target := 800, numerator := 193997425330571455280185344000 }, { target := 808, numerator := 978130856875938016426721280 }, { target := 890, numerator := 36679907132847675616002048 }, { target := 891, numerator := 7274903449896429573006950400 }, { target := 896, numerator := 7274903449896429573006950400 }, { target := 904, numerator := 36679907132847675616002048 }]

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
    Slot3.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 100512801270426332727083008 }, { target := 122, numerator := 16472112308222452478991400960 }, { target := 124, numerator := 169586774027109096458089922560 }, { target := 132, numerator := 16472112308222452478991400960 }, { target := 139, numerator := 100512801270426332727083008 }, { target := 196, numerator := 74849958392870673307402240 }, { target := 197, numerator := 12266466612506081633291468800 }, { target := 199, numerator := 126288023211676986724109516800 }, { target := 207, numerator := 12266466612506081633291468800 }, { target := 214, numerator := 74849958392870673307402240 }, { target := 231, numerator := 79127098872463283210682368 }, { target := 232, numerator := 12967407561792143440908124160 }, { target := 234, numerator := 133504481680915671679772917760 }, { target := 242, numerator := 12967407561792143440908124160 }, { target := 249, numerator := 79127098872463283210682368 }, { target := 337, numerator := 102651371510222637678723072 }, { target := 338, numerator := 16822582782865483382799728640 }, { target := 340, numerator := 173195003261728438935921623040 }, { target := 348, numerator := 16822582782865483382799728640 }, { target := 355, numerator := 102651371510222637678723072 }, { target := 412, numerator := 1375100664189024083904561152 }, { target := 413, numerator := 225352515195468871148754698240 }, { target := 415, numerator := 2320091397860237213245783408640 }, { target := 423, numerator := 225352515195468871148754698240 }, { target := 430, numerator := 1375100664189024083904561152 }, { target := 447, numerator := 2487157188883102658757394432 }, { target := 448, numerator := 407597162009844941129085091840 }, { target := 450, numerator := 4196370599862295301718267658240 }, { target := 458, numerator := 407597162009844941129085091840 }, { target := 465, numerator := 2487157188883102658757394432 }, { target := 508, numerator := 74849958392870673307402240 }, { target := 509, numerator := 12266466612506081633291468800 }, { target := 511, numerator := 126288023211676986724109516800 }, { target := 519, numerator := 12266466612506081633291468800 }, { target := 526, numerator := 74849958392870673307402240 }, { target := 543, numerator := 1375100664189024083904561152 }, { target := 544, numerator := 225352515195468871148754698240 }, { target := 546, numerator := 2320091397860237213245783408640 }, { target := 554, numerator := 225352515195468871148754698240 }, { target := 561, numerator := 1375100664189024083904561152 }, { target := 578, numerator := 81265669112259588162322432 }, { target := 579, numerator := 13317878036435174344716451840 }, { target := 581, numerator := 137112710915535014157604618240 }, { target := 589, numerator := 13317878036435174344716451840 }, { target := 596, numerator := 81265669112259588162322432 }, { target := 679, numerator := 81265669112259588162322432 }, { target := 680, numerator := 13317878036435174344716451840 }, { target := 682, numerator := 137112710915535014157604618240 }, { target := 690, numerator := 13317878036435174344716451840 }, { target := 697, numerator := 81265669112259588162322432 }, { target := 714, numerator := 79127098872463283210682368 }, { target := 715, numerator := 12967407561792143440908124160 }, { target := 717, numerator := 133504481680915671679772917760 }, { target := 725, numerator := 12967407561792143440908124160 }, { target := 732, numerator := 79127098872463283210682368 }, { target := 775, numerator := 79127098872463283210682368 }, { target := 776, numerator := 12967407561792143440908124160 }, { target := 778, numerator := 133504481680915671679772917760 }, { target := 786, numerator := 12967407561792143440908124160 }, { target := 793, numerator := 79127098872463283210682368 }]

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
    Slot4.Left9.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 212167762238159038367924224 }, { target := 252, numerator := 8482427768906686627674324992 }, { target := 255, numerator := 8482425695953821344563462144 }, { target := 262, numerator := 212167762238159038367924224 }, { target := 466, numerator := 5201532235516157069665239040 }, { target := 468, numerator := 207956293689325220549435064320 }, { target := 471, numerator := 207956242868545297479620362240 }, { target := 478, numerator := 5201532235516157069665239040 }, { target := 562, numerator := 3846396205736947727831400448 }, { target := 564, numerator := 153778206649211544669450665984 }, { target := 567, numerator := 153778169068582180504666636288 }, { target := 574, numerator := 3846396205736947727831400448 }, { target := 597, numerator := 4291264094300829582473822208 }, { target := 599, numerator := 171563942293693306953283928064 }, { target := 602, numerator := 171563900366549870420686798848 }, { target := 609, numerator := 4291264094300829582473822208 }, { target := 613, numerator := 3523879657279584200539766784 }, { target := 616, numerator := 12836650196055638792810266624 }, { target := 618, numerator := 3523882027686197672217149440 }, { target := 733, numerator := 212167762238159038367924224 }, { target := 735, numerator := 8482427768906686627674324992 }, { target := 738, numerator := 8482425695953821344563462144 }, { target := 745, numerator := 212167762238159038367924224 }, { target := 810, numerator := 2487157188883102658757394432 }, { target := 811, numerator := 407597162009844941129085091840 }, { target := 813, numerator := 4196370599862295301718267658240 }, { target := 821, numerator := 407597162009844941129085091840 }, { target := 828, numerator := 2487157188883102658757394432 }, { target := 829, numerator := 4284419972938308323171631104 }, { target := 831, numerator := 171290315591470510610455724032 }, { target := 834, numerator := 171290273731196521345055719424 }, { target := 841, numerator := 4284419972938308323171631104 }, { target := 845, numerator := 79127098872463283210682368 }, { target := 846, numerator := 12967407561792143440908124160 }, { target := 848, numerator := 133504481680915671679772917760 }, { target := 856, numerator := 12967407561792143440908124160 }, { target := 863, numerator := 79127098872463283210682368 }, { target := 864, numerator := 4359705307926042175495733248 }, { target := 866, numerator := 174300209315921270381565968384 }, { target := 869, numerator := 174300166720083361176997593088 }, { target := 876, numerator := 4359705307926042175495733248 }, { target := 906, numerator := 100512801270426332727083008 }, { target := 907, numerator := 16472112308222452478991400960 }, { target := 909, numerator := 169586774027109096458089922560 }, { target := 917, numerator := 16472112308222452478991400960 }, { target := 924, numerator := 100512801270426332727083008 }, { target := 925, numerator := 212167762238159038367924224 }, { target := 927, numerator := 8482427768906686627674324992 }, { target := 930, numerator := 8482425695953821344563462144 }, { target := 937, numerator := 212167762238159038367924224 }, { target := 941, numerator := 102651371510222637678723072 }, { target := 942, numerator := 16822582782865483382799728640 }, { target := 944, numerator := 173195003261728438935921623040 }, { target := 952, numerator := 16822582782865483382799728640 }, { target := 959, numerator := 102651371510222637678723072 }, { target := 960, numerator := 5201532235516157069665239040 }, { target := 962, numerator := 207956293689325220549435064320 }, { target := 965, numerator := 207956242868545297479620362240 }, { target := 972, numerator := 5201532235516157069665239040 }, { target := 986, numerator := 212167762238159038367924224 }, { target := 988, numerator := 8482427768906686627674324992 }, { target := 991, numerator := 8482425695953821344563462144 }, { target := 998, numerator := 212167762238159038367924224 }]

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
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 3523879657279584200539766784 }, { target := 2, numerator := 3513595961781686581277491200 }, { target := 3, numerator := 3489600672286592136332181504 }, { target := 4, numerator := 3513595961781686581277491200 }, { target := 10, numerator := 197535502773458415032205312 }, { target := 11, numerator := 4842805874446077271757291520 }, { target := 12, numerator := 3581127501893020298325786624 }, { target := 13, numerator := 3995314846418013749199765504 }, { target := 14, numerator := 197535502773458415032205312 }, { target := 15, numerator := 3988942733425321542263242752 }, { target := 16, numerator := 4059035976344935818564993024 }, { target := 17, numerator := 197535502773458415032205312 }, { target := 18, numerator := 4842805874446077271757291520 }, { target := 19, numerator := 197535502773458415032205312 }, { target := 51, numerator := 12836650196055638792810266624 }, { target := 52, numerator := 12799189154627460858590003200 }, { target := 53, numerator := 12711780057961712345409388544 }, { target := 54, numerator := 12799189154627460858590003200 }, { target := 55, numerator := 7897432750361397894731268096 }, { target := 56, numerator := 193614480331440722580508508160 }, { target := 57, numerator := 143172813087196955381902344192 }, { target := 58, numerator := 159731946273438596128919519232 }, { target := 59, numerator := 7897432750361397894731268096 }, { target := 60, numerator := 159477190378265647809734639616 }, { target := 61, numerator := 162279505225168079320768315392 }, { target := 62, numerator := 7897432750361397894731268096 }, { target := 63, numerator := 193614480331440722580508508160 }, { target := 64, numerator := 7897432750361397894731268096 }, { target := 140, numerator := 3523882027686197672217149440 }, { target := 141, numerator := 3513598325270771025313792000 }, { target := 142, numerator := 3489603019634775515872624640 }, { target := 143, numerator := 3513598325270771025313792000 }, { target := 144, numerator := 7897430820370799182869430272 }, { target := 145, numerator := 193614433015542173515508613120 }, { target := 146, numerator := 143172778098335133573310316544 }, { target := 147, numerator := 159731907237822293150294605824 }, { target := 148, numerator := 7897430820370799182869430272 }, { target := 149, numerator := 159477151404907106079879462912 }, { target := 150, numerator := 162279465566974163854446034944 }, { target := 151, numerator := 7897430820370799182869430272 }, { target := 152, numerator := 193614433015542173515508613120 }, { target := 153, numerator := 7897430820370799182869430272 }, { target := 482, numerator := 197535502773458415032205312 }, { target := 483, numerator := 4842805874446077271757291520 }, { target := 484, numerator := 3581127501893020298325786624 }, { target := 485, numerator := 3995314846418013749199765504 }, { target := 486, numerator := 197535502773458415032205312 }, { target := 487, numerator := 3988942733425321542263242752 }, { target := 488, numerator := 4059035976344935818564993024 }, { target := 489, numerator := 197535502773458415032205312 }, { target := 490, numerator := 4842805874446077271757291520 }, { target := 491, numerator := 197535502773458415032205312 }, { target := 880, numerator := 3513595961781686581277491200 }, { target := 883, numerator := 12799189154627460858590003200 }, { target := 885, numerator := 3513598325270771025313792000 }, { target := 976, numerator := 3489600672286592136332181504 }, { target := 979, numerator := 12711780057961712345409388544 }, { target := 981, numerator := 3489603019634775515872624640 }, { target := 1002, numerator := 3513595961781686581277491200 }, { target := 1005, numerator := 12799189154627460858590003200 }, { target := 1007, numerator := 3513598325270771025313792000 }]

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
    Slot10.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 103217181573666503114358784 }, { target := 35, numerator := 76863858618687821468139520 }, { target := 36, numerator := 81256079111184268409176064 }, { target := 37, numerator := 105413291819914726584877056 }, { target := 38, numerator := 1412098888337607691543248896 }, { target := 39, numerator := 2554076216386683896212750336 }, { target := 40, numerator := 76863858618687821468139520 }, { target := 41, numerator := 1412098888337607691543248896 }, { target := 42, numerator := 83452189357432491879694336 }, { target := 43, numerator := 83452189357432491879694336 }, { target := 44, numerator := 81256079111184268409176064 }, { target := 45, numerator := 81256079111184268409176064 }, { target := 46, numerator := 2554076216386683896212750336 }, { target := 47, numerator := 81256079111184268409176064 }, { target := 48, numerator := 103217181573666503114358784 }, { target := 49, numerator := 105413291819914726584877056 }, { target := 79, numerator := 16915308155080455684704174080 }, { target := 80, numerator := 12596506072932254233290342400 }, { target := 81, numerator := 13316306419956954475192647680 }, { target := 82, numerator := 17275208328592805805655326720 }, { target := 83, numerator := 231415811568441127771591147520 }, { target := 84, numerator := 418563901794863190666190520320 }, { target := 85, numerator := 12596506072932254233290342400 }, { target := 86, numerator := 231415811568441127771591147520 }, { target := 87, numerator := 13676206593469304596143800320 }, { target := 88, numerator := 13676206593469304596143800320 }, { target := 89, numerator := 13316306419956954475192647680 }, { target := 90, numerator := 13316306419956954475192647680 }, { target := 91, numerator := 418563901794863190666190520320 }, { target := 92, numerator := 13316306419956954475192647680 }, { target := 93, numerator := 16915308155080455684704174080 }, { target := 94, numerator := 17275208328592805805655326720 }, { target := 154, numerator := 174149646870887816542164090880 }, { target := 155, numerator := 129685907244278161254803046400 }, { target := 156, numerator := 137096530515379770469363220480 }, { target := 157, numerator := 177854958506438621149444177920 }, { target := 158, numerator := 2382515381659167362481095966720 }, { target := 159, numerator := 4309277432145585758266741227520 }, { target := 160, numerator := 129685907244278161254803046400 }, { target := 161, numerator := 2382515381659167362481095966720 }, { target := 162, numerator := 140801842150930575076643307520 }, { target := 163, numerator := 140801842150930575076643307520 }, { target := 164, numerator := 137096530515379770469363220480 }, { target := 165, numerator := 137096530515379770469363220480 }, { target := 166, numerator := 4309277432145585758266741227520 }, { target := 167, numerator := 137096530515379770469363220480 }, { target := 168, numerator := 174149646870887816542164090880 }, { target := 169, numerator := 177854958506438621149444177920 }, { target := 492, numerator := 16915308155080455684704174080 }, { target := 493, numerator := 12596506072932254233290342400 }, { target := 494, numerator := 13316306419956954475192647680 }, { target := 495, numerator := 17275208328592805805655326720 }, { target := 496, numerator := 231415811568441127771591147520 }, { target := 497, numerator := 418563901794863190666190520320 }, { target := 498, numerator := 12596506072932254233290342400 }, { target := 499, numerator := 231415811568441127771591147520 }, { target := 500, numerator := 13676206593469304596143800320 }, { target := 501, numerator := 13676206593469304596143800320 }, { target := 502, numerator := 13316306419956954475192647680 }, { target := 503, numerator := 13316306419956954475192647680 }, { target := 504, numerator := 418563901794863190666190520320 }, { target := 505, numerator := 13316306419956954475192647680 }, { target := 506, numerator := 16915308155080455684704174080 }, { target := 507, numerator := 17275208328592805805655326720 }]

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
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 36679907132847675616002048 }, { target := 122, numerator := 531858653426291296432029696 }, { target := 123, numerator := 941450949743090340810719232 }, { target := 124, numerator := 30566589277373063013335040 }, { target := 125, numerator := 586878514125562809856032768 }, { target := 126, numerator := 30566589277373063013335040 }, { target := 127, numerator := 935337631887615728208052224 }, { target := 128, numerator := 978130856875938016426721280 }, { target := 129, numerator := 586878514125562809856032768 }, { target := 130, numerator := 14983742063768275489136836608 }, { target := 131, numerator := 959790903309514178618720256 }, { target := 132, numerator := 531858653426291296432029696 }, { target := 133, numerator := 935337631887615728208052224 }, { target := 134, numerator := 30566589277373063013335040 }, { target := 135, numerator := 959790903309514178618720256 }, { target := 136, numerator := 30566589277373063013335040 }, { target := 137, numerator := 935337631887615728208052224 }, { target := 138, numerator := 978130856875938016426721280 }, { target := 139, numerator := 36679907132847675616002048 }, { target := 196, numerator := 7274903449896429573006950400 }, { target := 197, numerator := 105486100023498228808600780800 }, { target := 198, numerator := 186722521880675025707178393600 }, { target := 199, numerator := 6062419541580357977505792000 }, { target := 200, numerator := 116398455198342873168111206400 }, { target := 201, numerator := 6062419541580357977505792000 }, { target := 202, numerator := 185510037972358954111677235200 }, { target := 203, numerator := 193997425330571455280185344000 }, { target := 204, numerator := 116398455198342873168111206400 }, { target := 205, numerator := 2971798059282691480573339238400 }, { target := 206, numerator := 190359973605623240493681868800 }, { target := 207, numerator := 105486100023498228808600780800 }, { target := 208, numerator := 185510037972358954111677235200 }, { target := 209, numerator := 6062419541580357977505792000 }, { target := 210, numerator := 190359973605623240493681868800 }, { target := 211, numerator := 6062419541580357977505792000 }, { target := 212, numerator := 185510037972358954111677235200 }, { target := 213, numerator := 193997425330571455280185344000 }, { target := 214, numerator := 7274903449896429573006950400 }, { target := 890, numerator := 103217181573666503114358784 }, { target := 891, numerator := 76863858618687821468139520 }, { target := 892, numerator := 81256079111184268409176064 }, { target := 893, numerator := 105413291819914726584877056 }, { target := 894, numerator := 1412098888337607691543248896 }, { target := 895, numerator := 2554076216386683896212750336 }, { target := 896, numerator := 76863858618687821468139520 }, { target := 897, numerator := 1412098888337607691543248896 }, { target := 898, numerator := 83452189357432491879694336 }, { target := 899, numerator := 83452189357432491879694336 }, { target := 900, numerator := 81256079111184268409176064 }, { target := 901, numerator := 81256079111184268409176064 }, { target := 902, numerator := 2554076216386683896212750336 }, { target := 903, numerator := 81256079111184268409176064 }, { target := 904, numerator := 103217181573666503114358784 }, { target := 905, numerator := 105413291819914726584877056 }]

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
    Slot11.Left6.expected,
    Slot11.Left14.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 38109058253664781665828864 }, { target := 251, numerator := 43026356092847334138839040 }, { target := 252, numerator := 36879733793869143547576320 }, { target := 253, numerator := 485583161619277056709754880 }, { target := 254, numerator := 43026356092847334138839040 }, { target := 255, numerator := 36879733793869143547576320 }, { target := 256, numerator := 43026356092847334138839040 }, { target := 257, numerator := 43026356092847334138839040 }, { target := 258, numerator := 1783749791163470909584441344 }, { target := 259, numerator := 44255680552642972257091584 }, { target := 260, numerator := 485583161619277056709754880 }, { target := 261, numerator := 1783749791163470909584441344 }, { target := 262, numerator := 38109058253664781665828864 }, { target := 263, numerator := 43026356092847334138839040 }, { target := 264, numerator := 44255680552642972257091584 }, { target := 265, numerator := 43026356092847334138839040 }, { target := 508, numerator := 7274903449896429573006950400 }, { target := 509, numerator := 105486100023498228808600780800 }, { target := 510, numerator := 186722521880675025707178393600 }, { target := 511, numerator := 6062419541580357977505792000 }, { target := 512, numerator := 116398455198342873168111206400 }, { target := 513, numerator := 6062419541580357977505792000 }, { target := 514, numerator := 185510037972358954111677235200 }, { target := 515, numerator := 193997425330571455280185344000 }, { target := 516, numerator := 116398455198342873168111206400 }, { target := 517, numerator := 2971798059282691480573339238400 }, { target := 518, numerator := 190359973605623240493681868800 }, { target := 519, numerator := 105486100023498228808600780800 }, { target := 520, numerator := 185510037972358954111677235200 }, { target := 521, numerator := 6062419541580357977505792000 }, { target := 522, numerator := 190359973605623240493681868800 }, { target := 523, numerator := 6062419541580357977505792000 }, { target := 524, numerator := 185510037972358954111677235200 }, { target := 525, numerator := 193997425330571455280185344000 }, { target := 526, numerator := 7274903449896429573006950400 }, { target := 906, numerator := 36679907132847675616002048 }, { target := 907, numerator := 531858653426291296432029696 }, { target := 908, numerator := 941450949743090340810719232 }, { target := 909, numerator := 30566589277373063013335040 }, { target := 910, numerator := 586878514125562809856032768 }, { target := 911, numerator := 30566589277373063013335040 }, { target := 912, numerator := 935337631887615728208052224 }, { target := 913, numerator := 978130856875938016426721280 }, { target := 914, numerator := 586878514125562809856032768 }, { target := 915, numerator := 14983742063768275489136836608 }, { target := 916, numerator := 959790903309514178618720256 }, { target := 917, numerator := 531858653426291296432029696 }, { target := 918, numerator := 935337631887615728208052224 }, { target := 919, numerator := 30566589277373063013335040 }, { target := 920, numerator := 959790903309514178618720256 }, { target := 921, numerator := 30566589277373063013335040 }, { target := 922, numerator := 935337631887615728208052224 }, { target := 923, numerator := 978130856875938016426721280 }, { target := 924, numerator := 36679907132847675616002048 }]

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
    Slot12.Left2.expected,
    Slot12.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 562, numerator := 1722460103514474404080779264 }, { target := 563, numerator := 1944713020096987230413783040 }, { target := 564, numerator := 1666896874368846197497528320 }, { target := 565, numerator := 21947475512523141600384122880 }, { target := 566, numerator := 1944713020096987230413783040 }, { target := 567, numerator := 1666896874368846197497528320 }, { target := 568, numerator := 1944713020096987230413783040 }, { target := 569, numerator := 1944713020096987230413783040 }, { target := 570, numerator := 80622245490306527752297119744 }, { target := 571, numerator := 2000276249242615436997033984 }, { target := 572, numerator := 21947475512523141600384122880 }, { target := 573, numerator := 80622245490306527752297119744 }, { target := 574, numerator := 1722460103514474404080779264 }, { target := 575, numerator := 1944713020096987230413783040 }, { target := 576, numerator := 2000276249242615436997033984 }, { target := 577, numerator := 1944713020096987230413783040 }, { target := 925, numerator := 38312457818429026216181760 }, { target := 926, numerator := 43256000762742448953753600 }, { target := 927, numerator := 37076572082350670531788800 }, { target := 928, numerator := 488174865750950495335219200 }, { target := 929, numerator := 43256000762742448953753600 }, { target := 930, numerator := 37076572082350670531788800 }, { target := 931, numerator := 43256000762742448953753600 }, { target := 932, numerator := 43256000762742448953753600 }, { target := 933, numerator := 1793270203049694098054184960 }, { target := 934, numerator := 44491886498820804638146560 }, { target := 935, numerator := 488174865750950495335219200 }, { target := 936, numerator := 1793270203049694098054184960 }, { target := 937, numerator := 38312457818429026216181760 }, { target := 938, numerator := 43256000762742448953753600 }, { target := 939, numerator := 44491886498820804638146560 }, { target := 940, numerator := 43256000762742448953753600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent3
