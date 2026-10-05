import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk17Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 70; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent0

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
    Slot4.Left6.expected,
    Slot4.Left14.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 23970448648356185820364800 }, { target := 258, numerator := 426673985940740107602493440 }, { target := 259, numerator := 23970448648356185820364800 }, { target := 260, numerator := 379532103598972942155776000 }, { target := 261, numerator := 648001128460562223343861760 }, { target := 262, numerator := 23970448648356185820364800 }, { target := 263, numerator := 648001128460562223343861760 }, { target := 264, numerator := 648001128460562223343861760 }, { target := 265, numerator := 426673985940740107602493440 }, { target := 266, numerator := 23970448648356185820364800 }, { target := 353, numerator := 2007024928304220827686010880 }, { target := 354, numerator := 35725043723815130732810993664 }, { target := 355, numerator := 2007024928304220827686010880 }, { target := 356, numerator := 31777894698150163105028505600 }, { target := 357, numerator := 54256573895157436375111827456 }, { target := 358, numerator := 2007024928304220827686010880 }, { target := 359, numerator := 54256573895157436375111827456 }, { target := 360, numerator := 54256573895157436375111827456 }, { target := 361, numerator := 35725043723815130732810993664 }, { target := 362, numerator := 2007024928304220827686010880 }, { target := 389, numerator := 5488549194066072236214714368 }, { target := 391, numerator := 5488549194066072236214714368 }, { target := 656, numerator := 50233285656627071467391025152 }, { target := 658, numerator := 50233285656627071467391025152 }, { target := 695, numerator := 2007025654644768729999605760 }, { target := 696, numerator := 35725056652676883393992982528 }, { target := 697, numerator := 2007025654644768729999605760 }, { target := 698, numerator := 31777906198542171558327091200 }, { target := 699, numerator := 54256593530563581334322675712 }, { target := 700, numerator := 2007025654644768729999605760 }, { target := 701, numerator := 54256593530563581334322675712 }, { target := 702, numerator := 54256593530563581334322675712 }, { target := 703, numerator := 35725056652676883393992982528 }, { target := 704, numerator := 2007025654644768729999605760 }, { target := 731, numerator := 70407787788324691568790339584 }, { target := 733, numerator := 70407787788324691568790339584 }, { target := 745, numerator := 43598700758581986556603531264 }, { target := 747, numerator := 43598700758581986556603531264 }, { target := 872, numerator := 2098695222850996247289921536 }, { target := 874, numerator := 2098695222850996247289921536 }, { target := 947, numerator := 43531000912683567322819985408 }, { target := 949, numerator := 43531000912683567322819985408 }, { target := 961, numerator := 43734100450378825024170622976 }, { target := 963, numerator := 43734100450378825024170622976 }, { target := 982, numerator := 23969722307808283506769920 }, { target := 983, numerator := 426661057078987446420504576 }, { target := 984, numerator := 23969722307808283506769920 }, { target := 985, numerator := 379520603206964488857190400 }, { target := 986, numerator := 647981493054417264133013504 }, { target := 987, numerator := 23969722307808283506769920 }, { target := 988, numerator := 647981493054417264133013504 }, { target := 989, numerator := 647981493054417264133013504 }, { target := 990, numerator := 426661057078987446420504576 }, { target := 991, numerator := 23969722307808283506769920 }, { target := 992, numerator := 5488549194066072236214714368 }, { target := 994, numerator := 5488549194066072236214714368 }, { target := 1006, numerator := 50233285656627071467391025152 }, { target := 1008, numerator := 50233285656627071467391025152 }]

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
    Slot5.Left9.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 181971965198804088017387520 }, { target := 111, numerator := 216091708673579854520647680 }, { target := 112, numerator := 164912093461416204765757440 }, { target := 113, numerator := 1700300549826325697412464640 }, { target := 114, numerator := 204718460848654599019560960 }, { target := 115, numerator := 164912093461416204765757440 }, { target := 116, numerator := 204718460848654599019560960 }, { target := 117, numerator := 204718460848654599019560960 }, { target := 118, numerator := 8768774073017371991337861120 }, { target := 119, numerator := 204718460848654599019560960 }, { target := 120, numerator := 1700300549826325697412464640 }, { target := 121, numerator := 8768774073017371991337861120 }, { target := 122, numerator := 181971965198804088017387520 }, { target := 123, numerator := 204718460848654599019560960 }, { target := 124, numerator := 204718460848654599019560960 }, { target := 125, numerator := 216091708673579854520647680 }, { target := 206, numerator := 26876306965147302618275512320 }, { target := 207, numerator := 31915614521112421859202170880 }, { target := 208, numerator := 24356653187164742997812183040 }, { target := 209, numerator := 251125493205595108839511818240 }, { target := 210, numerator := 30235845335790715445559951360 }, { target := 211, numerator := 24356653187164742997812183040 }, { target := 212, numerator := 30235845335790715445559951360 }, { target := 213, numerator := 30235845335790715445559951360 }, { target := 214, numerator := 1295102041883035644918151249920 }, { target := 215, numerator := 30235845335790715445559951360 }, { target := 216, numerator := 251125493205595108839511818240 }, { target := 217, numerator := 1295102041883035644918151249920 }, { target := 218, numerator := 26876306965147302618275512320 }, { target := 219, numerator := 30235845335790715445559951360 }, { target := 220, numerator := 30235845335790715445559951360 }, { target := 221, numerator := 31915614521112421859202170880 }, { target := 257, numerator := 10433992852687629116768256000 }, { target := 260, numerator := 37326920523334603895734272000 }, { target := 262, numerator := 10433989384001122367176704000 }, { target := 302, numerator := 280127252746360460810177740800 }, { target := 303, numerator := 332651112636303047212086067200 }, { target := 304, numerator := 253865322801389167609223577600 }, { target := 305, numerator := 2617439017848805555695098265600 }, { target := 306, numerator := 315143159339655518411449958400 }, { target := 307, numerator := 253865322801389167609223577600 }, { target := 308, numerator := 315143159339655518411449958400 }, { target := 309, numerator := 315143159339655518411449958400 }, { target := 310, numerator := 13498631991715244705290439884800 }, { target := 311, numerator := 315143159339655518411449958400 }, { target := 312, numerator := 2617439017848805555695098265600 }, { target := 313, numerator := 13498631991715244705290439884800 }, { target := 314, numerator := 280127252746360460810177740800 }, { target := 315, numerator := 315143159339655518411449958400 }, { target := 316, numerator := 315143159339655518411449958400 }, { target := 317, numerator := 332651112636303047212086067200 }, { target := 353, numerator := 877386548765780176757850112000 }, { target := 356, numerator := 3138792448529156063304351744000 }, { target := 358, numerator := 877386257086561504154615808000 }, { target := 695, numerator := 877386337092868146903121920000 }, { target := 698, numerator := 3138791691283289036858327040000 }, { target := 700, numerator := 877386045413719843044065280000 }, { target := 982, numerator := 10434204525599658971496448000 }, { target := 985, numerator := 37327677769201630341758976000 }, { target := 987, numerator := 10434201056842783477727232000 }, { target := 1011, numerator := 2098695222850996247289921536 }, { target := 1013, numerator := 2098695222850996247289921536 }]

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
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 53733700645004841478237716480 }, { target := 260, numerator := 195441052072631803057904025600 }, { target := 262, numerator := 53733700645004841478237716480 }, { target := 353, numerator := 41792878279448210038629335040 }, { target := 356, numerator := 152009707167602513489480908800 }, { target := 358, numerator := 41792878279448210038629335040 }, { target := 379, numerator := 47763289462226525758433525760 }, { target := 382, numerator := 173725379620117158273692467200 }, { target := 384, numerator := 47763289462226525758433525760 }, { target := 524, numerator := 56121865118116167766159392768 }, { target := 527, numerator := 204127321053637660971588648960 }, { target := 529, numerator := 56121865118116167766159392768 }, { target := 620, numerator := 662715641288393044898265169920 }, { target := 623, numerator := 2410439642229125571047482982400 }, { target := 625, numerator := 662715641288393044898265169920 }, { target := 646, numerator := 1490214631221467603663126003712 }, { target := 649, numerator := 5420231844147655338139204976640 }, { target := 651, numerator := 1490214631221467603663126003712 }, { target := 679, numerator := 26876306965147302618275512320 }, { target := 680, numerator := 31915614521112421859202170880 }, { target := 681, numerator := 24356653187164742997812183040 }, { target := 682, numerator := 251125493205595108839511818240 }, { target := 683, numerator := 30235845335790715445559951360 }, { target := 684, numerator := 24356653187164742997812183040 }, { target := 685, numerator := 30235845335790715445559951360 }, { target := 686, numerator := 30235845335790715445559951360 }, { target := 687, numerator := 1295102041883035644918151249920 }, { target := 688, numerator := 30235845335790715445559951360 }, { target := 689, numerator := 251125493205595108839511818240 }, { target := 690, numerator := 1295102041883035644918151249920 }, { target := 691, numerator := 26876306965147302618275512320 }, { target := 692, numerator := 30235845335790715445559951360 }, { target := 693, numerator := 30235845335790715445559951360 }, { target := 694, numerator := 31915614521112421859202170880 }, { target := 695, numerator := 41792878279448210038629335040 }, { target := 698, numerator := 152009707167602513489480908800 }, { target := 700, numerator := 41792878279448210038629335040 }, { target := 721, numerator := 662715641288393044898265169920 }, { target := 724, numerator := 2410439642229125571047482982400 }, { target := 726, numerator := 662715641288393044898265169920 }, { target := 735, numerator := 47763289462226525758433525760 }, { target := 738, numerator := 173725379620117158273692467200 }, { target := 740, numerator := 47763289462226525758433525760 }, { target := 836, numerator := 46569207225670862614472687616 }, { target := 839, numerator := 169382245129614229316850155520 }, { target := 841, numerator := 46569207225670862614472687616 }, { target := 966, numerator := 181971965198804088017387520 }, { target := 967, numerator := 216091708673579854520647680 }, { target := 968, numerator := 164912093461416204765757440 }, { target := 969, numerator := 1700300549826325697412464640 }, { target := 970, numerator := 204718460848654599019560960 }, { target := 971, numerator := 164912093461416204765757440 }, { target := 972, numerator := 204718460848654599019560960 }, { target := 973, numerator := 204718460848654599019560960 }, { target := 974, numerator := 8768774073017371991337861120 }, { target := 975, numerator := 204718460848654599019560960 }, { target := 976, numerator := 1700300549826325697412464640 }, { target := 977, numerator := 8768774073017371991337861120 }, { target := 978, numerator := 181971965198804088017387520 }, { target := 979, numerator := 204718460848654599019560960 }, { target := 980, numerator := 204718460848654599019560960 }, { target := 981, numerator := 216091708673579854520647680 }]

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
    Slot8.Left10.expected,
    Slot8.Left11.expected,
    Slot8.Left12.expected,
    Slot8.Left13.expected,
    Slot8.Left14.expected,
    Slot8.Left15.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 1795246541092891155140444160 }, { target := 57, numerator := 30160141890360571406359461888 }, { target := 58, numerator := 65346974095781238047112167424 }, { target := 59, numerator := 2154295849311469386168532992 }, { target := 60, numerator := 34468733588983510178696527872 }, { target := 61, numerator := 2513345157530047617196621824 }, { target := 62, numerator := 65346974095781238047112167424 }, { target := 63, numerator := 65346974095781238047112167424 }, { target := 64, numerator := 34468733588983510178696527872 }, { target := 65, numerator := 806424746258926706889087516672 }, { target := 66, numerator := 64628875479344081585055989760 }, { target := 67, numerator := 30160141890360571406359461888 }, { target := 68, numerator := 65346974095781238047112167424 }, { target := 69, numerator := 2513345157530047617196621824 }, { target := 70, numerator := 64628875479344081585055989760 }, { target := 71, numerator := 2513345157530047617196621824 }, { target := 72, numerator := 65346974095781238047112167424 }, { target := 73, numerator := 65346974095781238047112167424 }, { target := 74, numerator := 2154295849311469386168532992 }, { target := 110, numerator := 1365605637742820494709620736 }, { target := 112, numerator := 50429999411877947177309306880 }, { target := 115, numerator := 50429987062843387541010251776 }, { target := 122, numerator := 1365617986777380131008675840 }, { target := 206, numerator := 218015106896005455218162532352 }, { target := 208, numerator := 8051007852251278644139429724160 }, { target := 211, numerator := 8051005880762574166046258757632 }, { target := 218, numerator := 218017078384709933311333498880 }, { target := 302, numerator := 2175462915511541517012258783232 }, { target := 304, numerator := 80336951252738120558609757634560 }, { target := 307, numerator := 80336931580245576324891344371712 }, { target := 314, numerator := 2175482588004085750730672046080 }, { target := 679, numerator := 218015106896005455218162532352 }, { target := 681, numerator := 8051007852251278644139429724160 }, { target := 684, numerator := 8051005880762574166046258757632 }, { target := 691, numerator := 218017078384709933311333498880 }, { target := 862, numerator := 46569207225670862614472687616 }, { target := 865, numerator := 169382245129614229316850155520 }, { target := 867, numerator := 46569207225670862614472687616 }, { target := 911, numerator := 46569207225670862614472687616 }, { target := 914, numerator := 169382245129614229316850155520 }, { target := 916, numerator := 46569207225670862614472687616 }, { target := 937, numerator := 1490214631221467603663126003712 }, { target := 940, numerator := 5420231844147655338139204976640 }, { target := 942, numerator := 1490214631221467603663126003712 }, { target := 951, numerator := 46569207225670862614472687616 }, { target := 954, numerator := 169382245129614229316850155520 }, { target := 956, numerator := 46569207225670862614472687616 }, { target := 966, numerator := 1365449817838924691367002112 }, { target := 968, numerator := 50424245190128531619666984960 }, { target := 971, numerator := 50424232842503035716781473792 }, { target := 978, numerator := 1365462165464420594252513280 }, { target := 982, numerator := 53733700645004841478237716480 }, { target := 985, numerator := 195441052072631803057904025600 }, { target := 987, numerator := 53733700645004841478237716480 }, { target := 996, numerator := 56121865118116167766159392768 }, { target := 999, numerator := 204127321053637660971588648960 }, { target := 1001, numerator := 56121865118116167766159392768 }]

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
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 1787724558378814795551866880 }, { target := 112, numerator := 67169404192439633329688412160 }, { target := 115, numerator := 67164324028297023995584184320 }, { target := 122, numerator := 1792804722521424129656094720 }, { target := 152, numerator := 67452024406433067972029317120 }, { target := 153, numerator := 1133194010028075541930092527616 }, { target := 154, numerator := 2455253688394163674181867143168 }, { target := 155, numerator := 80942429287719681566435180544 }, { target := 156, numerator := 1295078868603514905062962888704 }, { target := 157, numerator := 94432834169006295160841043968 }, { target := 158, numerator := 2455253688394163674181867143168 }, { target := 159, numerator := 2455253688394163674181867143168 }, { target := 160, numerator := 1295078868603514905062962888704 }, { target := 161, numerator := 30299449363369734133035569250304 }, { target := 162, numerator := 2428272878631590446993055416320 }, { target := 163, numerator := 1133194010028075541930092527616 }, { target := 164, numerator := 2455253688394163674181867143168 }, { target := 165, numerator := 94432834169006295160841043968 }, { target := 166, numerator := 2428272878631590446993055416320 }, { target := 167, numerator := 94432834169006295160841043968 }, { target := 168, numerator := 2455253688394163674181867143168 }, { target := 169, numerator := 2455253688394163674181867143168 }, { target := 170, numerator := 80942429287719681566435180544 }, { target := 283, numerator := 67446922867125763226982154240 }, { target := 284, numerator := 1133108304167712822213300191232 }, { target := 285, numerator := 2455067992363377781462150414336 }, { target := 286, numerator := 80936307440550915872378585088 }, { target := 287, numerator := 1294980919048814653958057361408 }, { target := 288, numerator := 94425692013976068517775015936 }, { target := 289, numerator := 2455067992363377781462150414336 }, { target := 290, numerator := 2455067992363377781462150414336 }, { target := 291, numerator := 1294980919048814653958057361408 }, { target := 292, numerator := 30297157751912892841560383684608 }, { target := 293, numerator := 2428089223216527476171357552640 }, { target := 294, numerator := 1133108304167712822213300191232 }, { target := 295, numerator := 2455067992363377781462150414336 }, { target := 296, numerator := 94425692013976068517775015936 }, { target := 297, numerator := 2428089223216527476171357552640 }, { target := 298, numerator := 94425692013976068517775015936 }, { target := 299, numerator := 2455067992363377781462150414336 }, { target := 300, numerator := 2455067992363377781462150414336 }, { target := 301, numerator := 80936307440550915872378585088 }, { target := 660, numerator := 1800348080400195900187607040 }, { target := 661, numerator := 30245847750723291123151798272 }, { target := 662, numerator := 65532670126567130766828896256 }, { target := 663, numerator := 2160417696480235080225128448 }, { target := 664, numerator := 34566683143683761283602055168 }, { target := 665, numerator := 2520487312560274260262649856 }, { target := 666, numerator := 65532670126567130766828896256 }, { target := 667, numerator := 65532670126567130766828896256 }, { target := 668, numerator := 34566683143683761283602055168 }, { target := 669, numerator := 808716357715767998364273082368 }, { target := 670, numerator := 64812530894407052406753853440 }, { target := 671, numerator := 30245847750723291123151798272 }, { target := 672, numerator := 65532670126567130766828896256 }, { target := 673, numerator := 2520487312560274260262649856 }, { target := 674, numerator := 64812530894407052406753853440 }, { target := 675, numerator := 2520487312560274260262649856 }, { target := 676, numerator := 65532670126567130766828896256 }, { target := 677, numerator := 65532670126567130766828896256 }, { target := 678, numerator := 2160417696480235080225128448 }]

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
    Slot11.Left12.expected,
    Slot11.Left13.expected,
    Slot11.Left14.expected,
    Slot11.Left15.expected,
    Slot11.Left16.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 206, numerator := 30033772580764088565271363584 }, { target := 208, numerator := 1128445990432985839938765324288 }, { target := 211, numerator := 1128360643675390003125814296576 }, { target := 218, numerator := 30119119338359925378222391296 }, { target := 241, numerator := 65073173924988858558087954432 }, { target := 243, numerator := 2444966312604802653200658202624 }, { target := 246, numerator := 2444781394630011673439264309248 }, { target := 253, numerator := 65258091899779838319481847808 }, { target := 302, numerator := 2145269470054577754662240256 }, { target := 304, numerator := 80603285030927559995626094592 }, { target := 307, numerator := 80597188833956428794701021184 }, { target := 314, numerator := 2151365667025708955587313664 }, { target := 337, numerator := 34324311520873244074595844096 }, { target := 339, numerator := 1289652560494840959930017513472 }, { target := 342, numerator := 1289555021343302860715216338944 }, { target := 349, numerator := 34421850672411343289397018624 }, { target := 363, numerator := 2502814381730340713772613632 }, { target := 365, numerator := 94037165869415486661563777024 }, { target := 368, numerator := 94030053639615833593817858048 }, { target := 375, numerator := 2509926611529993781518532608 }, { target := 473, numerator := 65073173924988858558087954432 }, { target := 475, numerator := 2444966312604802653200658202624 }, { target := 478, numerator := 2444781394630011673439264309248 }, { target := 485, numerator := 65258091899779838319481847808 }, { target := 508, numerator := 65073173924988858558087954432 }, { target := 510, numerator := 2444966312604802653200658202624 }, { target := 513, numerator := 2444781394630011673439264309248 }, { target := 520, numerator := 65258091899779838319481847808 }, { target := 569, numerator := 34324311520873244074595844096 }, { target := 571, numerator := 1289652560494840959930017513472 }, { target := 574, numerator := 1289555021343302860715216338944 }, { target := 581, numerator := 34421850672411343289397018624 }, { target := 604, numerator := 803045871623763606161898602496 }, { target := 606, numerator := 30172496363243883291696034742272 }, { target := 609, numerator := 30170214353511023178816415596544 }, { target := 616, numerator := 805327881356623719041517748224 }, { target := 630, numerator := 64358084101637332639867207680 }, { target := 632, numerator := 2418098550927826799868782837760 }, { target := 635, numerator := 2417915665018692863841030635520 }, { target := 642, numerator := 64540970010771268667619409920 }, { target := 679, numerator := 30033772580764088565271363584 }, { target := 681, numerator := 1128445990432985839938765324288 }, { target := 684, numerator := 1128360643675390003125814296576 }, { target := 691, numerator := 30119119338359925378222391296 }, { target := 705, numerator := 65073173924988858558087954432 }, { target := 707, numerator := 2444966312604802653200658202624 }, { target := 710, numerator := 2444781394630011673439264309248 }, { target := 717, numerator := 65258091899779838319481847808 }, { target := 785, numerator := 2502814381730340713772613632 }, { target := 787, numerator := 94037165869415486661563777024 }, { target := 790, numerator := 94030053639615833593817858048 }, { target := 797, numerator := 2509926611529993781518532608 }, { target := 820, numerator := 64358084101637332639867207680 }, { target := 822, numerator := 2418098550927826799868782837760 }, { target := 825, numerator := 2417915665018692863841030635520 }, { target := 832, numerator := 64540970010771268667619409920 }, { target := 846, numerator := 2502814381730340713772613632 }, { target := 848, numerator := 94037165869415486661563777024 }, { target := 851, numerator := 94030053639615833593817858048 }, { target := 858, numerator := 2509926611529993781518532608 }, { target := 895, numerator := 65073173924988858558087954432 }, { target := 897, numerator := 2444966312604802653200658202624 }, { target := 900, numerator := 2444781394630011673439264309248 }, { target := 907, numerator := 65258091899779838319481847808 }]

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
    Slot11.Left17.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 52652850344674284322066268160 }, { target := 15, numerator := 40952216934746665583829319680 }, { target := 16, numerator := 46802533639710474952947793920 }, { target := 17, numerator := 54992977026659808069713657856 }, { target := 18, numerator := 649385154250982839972150640640 }, { target := 19, numerator := 1460239049558966818531971170304 }, { target := 20, numerator := 40952216934746665583829319680 }, { target := 21, numerator := 649385154250982839972150640640 }, { target := 22, numerator := 46802533639710474952947793920 }, { target := 23, numerator := 45632470298717713079124099072 }, { target := 24, numerator := 45632470298717713079124099072 }, { target := 25, numerator := 45632470298717713079124099072 }, { target := 26, numerator := 1460239049558966818531971170304 }, { target := 27, numerator := 45632470298717713079124099072 }, { target := 28, numerator := 52652850344674284322066268160 }, { target := 29, numerator := 54992977026659808069713657856 }, { target := 56, numerator := 1369970338143117164289196032 }, { target := 57, numerator := 218711919063471713165324058624 }, { target := 59, numerator := 2182416053076100978512897245184 }, { target := 67, numerator := 218711919063471713165324058624 }, { target := 74, numerator := 1369814020213160167807647744 }, { target := 136, numerator := 191509766542435186329727795200 }, { target := 137, numerator := 148952040644116256034232729600 }, { target := 138, numerator := 170230903593275721181980262400 }, { target := 139, numerator := 200021311722098972388826808320 }, { target := 140, numerator := 2361953787356700631399976140800 }, { target := 141, numerator := 5311204192110202500877784186880 }, { target := 142, numerator := 148952040644116256034232729600 }, { target := 143, numerator := 2361953787356700631399976140800 }, { target := 144, numerator := 170230903593275721181980262400 }, { target := 145, numerator := 165975131003443828152430755840 }, { target := 146, numerator := 165975131003443828152430755840 }, { target := 147, numerator := 165975131003443828152430755840 }, { target := 148, numerator := 5311204192110202500877784186880 }, { target := 149, numerator := 165975131003443828152430755840 }, { target := 150, numerator := 191509766542435186329727795200 }, { target := 151, numerator := 200021311722098972388826808320 }, { target := 152, numerator := 50591181990901128790341058560 }, { target := 153, numerator := 8076740198562908779638077521920 }, { target := 155, numerator := 80593721372603044635505034526720 }, { target := 163, numerator := 8076740198562908779638077521920 }, { target := 170, numerator := 50585409377711842947256811520 }, { target := 283, numerator := 50591169602397022019766976512 }, { target := 284, numerator := 8076738220773001890108731817984 }, { target := 286, numerator := 80593701637233976089413570002944 }, { target := 294, numerator := 8076738220773001890108731817984 }, { target := 301, numerator := 50585396990621303509723643904 }, { target := 660, numerator := 1369982726647223934863278080 }, { target := 661, numerator := 218713896853378602694669762560 }, { target := 663, numerator := 2182435788445169524604361768960 }, { target := 671, numerator := 218713896853378602694669762560 }, { target := 678, numerator := 1369826407303699605340815360 }, { target := 921, numerator := 65073173924988858558087954432 }, { target := 923, numerator := 2444966312604802653200658202624 }, { target := 926, numerator := 2444781394630011673439264309248 }, { target := 933, numerator := 65258091899779838319481847808 }, { target := 966, numerator := 2145269470054577754662240256 }, { target := 968, numerator := 80603285030927559995626094592 }, { target := 971, numerator := 80597188833956428794701021184 }, { target := 978, numerator := 2151365667025708955587313664 }]

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
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 181971965198804088017387520 }, { target := 57, numerator := 26876306965147302618275512320 }, { target := 59, numerator := 280127252746360460810177740800 }, { target := 67, numerator := 26876306965147302618275512320 }, { target := 74, numerator := 181971965198804088017387520 }, { target := 91, numerator := 216091708673579854520647680 }, { target := 92, numerator := 31915614521112421859202170880 }, { target := 94, numerator := 332651112636303047212086067200 }, { target := 102, numerator := 31915614521112421859202170880 }, { target := 109, numerator := 216091708673579854520647680 }, { target := 152, numerator := 164912093461416204765757440 }, { target := 153, numerator := 24356653187164742997812183040 }, { target := 155, numerator := 253865322801389167609223577600 }, { target := 163, numerator := 24356653187164742997812183040 }, { target := 170, numerator := 164912093461416204765757440 }, { target := 187, numerator := 1700300549826325697412464640 }, { target := 188, numerator := 251125493205595108839511818240 }, { target := 190, numerator := 2617439017848805555695098265600 }, { target := 198, numerator := 251125493205595108839511818240 }, { target := 205, numerator := 1700300549826325697412464640 }, { target := 222, numerator := 204718460848654599019560960 }, { target := 223, numerator := 30235845335790715445559951360 }, { target := 225, numerator := 315143159339655518411449958400 }, { target := 233, numerator := 30235845335790715445559951360 }, { target := 240, numerator := 204718460848654599019560960 }, { target := 267, numerator := 52652850344674284322066268160 }, { target := 268, numerator := 40952216934746665583829319680 }, { target := 269, numerator := 46802533639710474952947793920 }, { target := 270, numerator := 54992977026659808069713657856 }, { target := 271, numerator := 649385154250982839972150640640 }, { target := 272, numerator := 1460239049558966818531971170304 }, { target := 273, numerator := 40952216934746665583829319680 }, { target := 274, numerator := 649385154250982839972150640640 }, { target := 275, numerator := 46802533639710474952947793920 }, { target := 276, numerator := 45632470298717713079124099072 }, { target := 277, numerator := 45632470298717713079124099072 }, { target := 278, numerator := 45632470298717713079124099072 }, { target := 279, numerator := 1460239049558966818531971170304 }, { target := 280, numerator := 45632470298717713079124099072 }, { target := 281, numerator := 52652850344674284322066268160 }, { target := 282, numerator := 54992977026659808069713657856 }, { target := 283, numerator := 164912093461416204765757440 }, { target := 284, numerator := 24356653187164742997812183040 }, { target := 286, numerator := 253865322801389167609223577600 }, { target := 294, numerator := 24356653187164742997812183040 }, { target := 301, numerator := 164912093461416204765757440 }, { target := 318, numerator := 204718460848654599019560960 }, { target := 319, numerator := 30235845335790715445559951360 }, { target := 321, numerator := 315143159339655518411449958400 }, { target := 329, numerator := 30235845335790715445559951360 }, { target := 336, numerator := 204718460848654599019560960 }, { target := 419, numerator := 204718460848654599019560960 }, { target := 420, numerator := 30235845335790715445559951360 }, { target := 422, numerator := 315143159339655518411449958400 }, { target := 430, numerator := 30235845335790715445559951360 }, { target := 437, numerator := 204718460848654599019560960 }, { target := 454, numerator := 8768774073017371991337861120 }, { target := 455, numerator := 1295102041883035644918151249920 }, { target := 457, numerator := 13498631991715244705290439884800 }, { target := 465, numerator := 1295102041883035644918151249920 }, { target := 472, numerator := 8768774073017371991337861120 }]

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
    Slot14.Left9.expected,
    Slot14.Left10.expected,
    Slot14.Left11.expected,
    Slot14.Left12.expected,
    Slot14.Left13.expected,
    Slot14.Left14.expected,
    Slot14.Left15.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 2098695222850996247289921536 }, { target := 5, numerator := 50233285656627071467391025152 }, { target := 6, numerator := 37573414473622674749867950080 }, { target := 7, numerator := 43598700758581986556603531264 }, { target := 8, numerator := 2098695222850996247289921536 }, { target := 9, numerator := 43531000912683567322819985408 }, { target := 10, numerator := 43734100450378825024170622976 }, { target := 11, numerator := 2098695222850996247289921536 }, { target := 12, numerator := 50233285656627071467391025152 }, { target := 13, numerator := 2098695222850996247289921536 }, { target := 14, numerator := 10350520909866128083834109952 }, { target := 15, numerator := 870367456375653935343787311104 }, { target := 20, numerator := 870367246396125201727896944640 }, { target := 28, numerator := 10350730889394861699724476416 }, { target := 136, numerator := 37028305159147927064568397824 }, { target := 137, numerator := 3113682108940922814797916930048 }, { target := 142, numerator := 3113681357753022724563460423680 }, { target := 150, numerator := 37029056347048017299024904192 }, { target := 267, numerator := 10350517468929113388239290368 }, { target := 268, numerator := 870367167029869012121378881536 }, { target := 273, numerator := 870366957050410084299712757760 }, { target := 281, numerator := 10350727448388041209905414144 }, { target := 489, numerator := 204718460848654599019560960 }, { target := 490, numerator := 30235845335790715445559951360 }, { target := 492, numerator := 315143159339655518411449958400 }, { target := 500, numerator := 30235845335790715445559951360 }, { target := 507, numerator := 204718460848654599019560960 }, { target := 550, numerator := 1700300549826325697412464640 }, { target := 551, numerator := 251125493205595108839511818240 }, { target := 553, numerator := 2617439017848805555695098265600 }, { target := 561, numerator := 251125493205595108839511818240 }, { target := 568, numerator := 1700300549826325697412464640 }, { target := 585, numerator := 8768774073017371991337861120 }, { target := 586, numerator := 1295102041883035644918151249920 }, { target := 588, numerator := 13498631991715244705290439884800 }, { target := 596, numerator := 1295102041883035644918151249920 }, { target := 603, numerator := 8768774073017371991337861120 }, { target := 660, numerator := 181971965198804088017387520 }, { target := 661, numerator := 26876306965147302618275512320 }, { target := 663, numerator := 280127252746360460810177740800 }, { target := 671, numerator := 26876306965147302618275512320 }, { target := 678, numerator := 181971965198804088017387520 }, { target := 766, numerator := 204718460848654599019560960 }, { target := 767, numerator := 30235845335790715445559951360 }, { target := 769, numerator := 315143159339655518411449958400 }, { target := 777, numerator := 30235845335790715445559951360 }, { target := 784, numerator := 204718460848654599019560960 }, { target := 801, numerator := 204718460848654599019560960 }, { target := 802, numerator := 30235845335790715445559951360 }, { target := 804, numerator := 315143159339655518411449958400 }, { target := 812, numerator := 30235845335790715445559951360 }, { target := 819, numerator := 204718460848654599019560960 }, { target := 876, numerator := 216091708673579854520647680 }, { target := 877, numerator := 31915614521112421859202170880 }, { target := 879, numerator := 332651112636303047212086067200 }, { target := 887, numerator := 31915614521112421859202170880 }, { target := 894, numerator := 216091708673579854520647680 }]

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
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot17.Left4.expected,
    Slot17.Left5.expected,
    Slot17.Left6.expected,
    Slot17.Left7.expected,
    Slot17.Left8.expected,
    Slot17.Left9.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 3389853971215075988924792832 }, { target := 6, numerator := 32834373314702016818922389504 }, { target := 11, numerator := 3389853971215075988924792832 }, { target := 14, numerator := 23970448648356185820364800 }, { target := 15, numerator := 2007024928304220827686010880 }, { target := 20, numerator := 2007025654644768729999605760 }, { target := 28, numerator := 23969722307808283506769920 }, { target := 40, numerator := 426673985940740107602493440 }, { target := 41, numerator := 35725043723815130732810993664 }, { target := 46, numerator := 35725056652676883393992982528 }, { target := 54, numerator := 426661057078987446420504576 }, { target := 75, numerator := 23970448648356185820364800 }, { target := 76, numerator := 2007024928304220827686010880 }, { target := 81, numerator := 2007025654644768729999605760 }, { target := 89, numerator := 23969722307808283506769920 }, { target := 126, numerator := 5488549194066072236214714368 }, { target := 127, numerator := 50233285656627071467391025152 }, { target := 128, numerator := 70407787788324691568790339584 }, { target := 129, numerator := 43598700758581986556603531264 }, { target := 130, numerator := 2098695222850996247289921536 }, { target := 131, numerator := 43531000912683567322819985408 }, { target := 132, numerator := 43734100450378825024170622976 }, { target := 133, numerator := 5488549194066072236214714368 }, { target := 134, numerator := 50233285656627071467391025152 }, { target := 135, numerator := 2098695222850996247289921536 }, { target := 136, numerator := 379532103598972942155776000 }, { target := 137, numerator := 31777894698150163105028505600 }, { target := 142, numerator := 31777906198542171558327091200 }, { target := 150, numerator := 379520603206964488857190400 }, { target := 171, numerator := 648001128460562223343861760 }, { target := 172, numerator := 54256573895157436375111827456 }, { target := 177, numerator := 54256593530563581334322675712 }, { target := 185, numerator := 647981493054417264133013504 }, { target := 267, numerator := 23970448648356185820364800 }, { target := 268, numerator := 2007024928304220827686010880 }, { target := 273, numerator := 2007025654644768729999605760 }, { target := 281, numerator := 23969722307808283506769920 }, { target := 403, numerator := 648001128460562223343861760 }, { target := 404, numerator := 54256573895157436375111827456 }, { target := 409, numerator := 54256593530563581334322675712 }, { target := 417, numerator := 647981493054417264133013504 }, { target := 438, numerator := 648001128460562223343861760 }, { target := 439, numerator := 54256573895157436375111827456 }, { target := 444, numerator := 54256593530563581334322675712 }, { target := 452, numerator := 647981493054417264133013504 }, { target := 534, numerator := 426673985940740107602493440 }, { target := 535, numerator := 35725043723815130732810993664 }, { target := 540, numerator := 35725056652676883393992982528 }, { target := 548, numerator := 426661057078987446420504576 }, { target := 750, numerator := 23970448648356185820364800 }, { target := 751, numerator := 2007024928304220827686010880 }, { target := 756, numerator := 2007025654644768729999605760 }, { target := 764, numerator := 23969722307808283506769920 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent0
