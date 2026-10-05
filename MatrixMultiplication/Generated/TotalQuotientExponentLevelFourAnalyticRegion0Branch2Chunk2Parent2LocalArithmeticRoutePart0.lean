import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk2Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk2.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left6.expected,
    Slot11.Left14.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 1971821157387835893874688 }, { target := 72, numerator := 52392951972658066044747776 }, { target := 74, numerator := 690286337694119448585175040 }, { target := 82, numerator := 52253522599006079148883968 }, { target := 89, numerator := 1940325552023493966561280 }, { target := 146, numerator := 13649952186232216991301632 }, { target := 147, numerator := 371680301671771696623779840 }, { target := 149, numerator := 4426631508665156596781809664 }, { target := 157, numerator := 371682470150207200913522688 }, { target := 164, numerator := 13645925011994851881779200 }, { target := 200, numerator := 21420989026251745800486912 }, { target := 202, numerator := 765121049945055518332551168 }, { target := 205, numerator := 765296828577239254091956224 }, { target := 212, numerator := 21205019727746650683211776 }, { target := 242, numerator := 179589278918310459839873024 }, { target := 243, numerator := 4890112174363481215997050880 }, { target := 245, numerator := 58240171821267350757570510848 }, { target := 253, numerator := 4890140704535108844011913216 }, { target := 260, numerator := 179536294313859150669414400 }, { target := 296, numerator := 1057970197300007094416572416 }, { target := 298, numerator := 37772248959370623281669341184 }, { target := 301, numerator := 37781088980667696564909637632 }, { target := 308, numerator := 1047182259318486410322771968 }, { target := 640, numerator := 13649629717802848148783104 }, { target := 641, numerator := 371671521042984709107220480 }, { target := 643, numerator := 4426526933287124602357547008 }, { target := 651, numerator := 371673689470191767635623936 }, { target := 658, numerator := 13645602638704025167462400 }, { target := 659, numerator := 1057823658597745061007458304 }, { target := 661, numerator := 37767262424141873481496133632 }, { target := 664, numerator := 37776098885258435885392723968 }, { target := 671, numerator := 1047039003925000314727432192 }, { target := 1017, numerator := 596392957485775436382208 }, { target := 1018, numerator := 16239435225041604664360960 }, { target := 1020, numerator := 193408139540249380195926016 }, { target := 1028, numerator := 16239529970081715424591872 }, { target := 1035, numerator := 596217002411284024524800 }, { target := 1036, numerator := 21473321725368318860197888 }, { target := 1038, numerator := 766830030446701212596174848 }, { target := 1041, numerator := 767007764632478095125774336 }, { target := 1048, numerator := 21255655867966297655476224 }]

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
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 10766477088836041316499456 }, { target := 30, numerator := 541490325949238088541667328 }, { target := 35, numerator := 541271710260156656762486784 }, { target := 43, numerator := 10886613684010269861216256 }, { target := 71, numerator := 596380554853876634746880 }, { target := 72, numerator := 13649952186232216991301632 }, { target := 74, numerator := 179589278918310459839873024 }, { target := 82, numerator := 13649629717802848148783104 }, { target := 89, numerator := 596392957485775436382208 }, { target := 104, numerator := 375414394708078253454655488 }, { target := 105, numerator := 18881130873096955827578732544 }, { target := 110, numerator := 18873508001110789008792748032 }, { target := 118, numerator := 379603416501138911173541888 }, { target := 146, numerator := 52392951972658066044747776 }, { target := 147, numerator := 1321994833759789945834176512 }, { target := 149, numerator := 17950805195093001175606231040 }, { target := 157, numerator := 1318318621327042026391207936 }, { target := 164, numerator := 51570043517229966945157120 }, { target := 226, numerator := 375589839269715555335012352 }, { target := 227, numerator := 18889954700248876545396965376 }, { target := 232, numerator := 18882328265822236259257417728 }, { target := 240, numerator := 379780818742349858919677952 }, { target := 242, numerator := 690286337694119448585175040 }, { target := 243, numerator := 17487324529394676556390989824 }, { target := 245, numerator := 237740428233144986431964315648 }, { target := 253, numerator := 17436816430395101556074610688 }, { target := 260, numerator := 678976036861611410578210816 }, { target := 624, numerator := 10591216672632103174668288 }, { target := 625, numerator := 532675760227022876593618944 }, { target := 630, numerator := 532460703239301321543647232 }, { target := 638, numerator := 10709397643000015841394688 }, { target := 640, numerator := 52253522599006079148883968 }, { target := 641, numerator := 1318329570434264518197510144 }, { target := 643, numerator := 17900430201643085797728976896 }, { target := 651, numerator := 1314667511218056406367207424 }, { target := 658, numerator := 51433791198083484380823552 }, { target := 1017, numerator := 1940325552023493966561280 }, { target := 1018, numerator := 48976533304183214162575360 }, { target := 1020, numerator := 665104191635221181051699200 }, { target := 1028, numerator := 48839863866705794123694080 }, { target := 1035, numerator := 1909731465410610043289600 }]

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
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 10654511937415704483987456 }, { target := 30, numerator := 516479871350769005874905088 }, { target := 35, numerator := 516551948337588404244971520 }, { target := 43, numerator := 10586708041358048998981632 }, { target := 104, numerator := 389706655236977264877895680 }, { target := 105, numerator := 18891118086273667454090608640 }, { target := 110, numerator := 18893754423031084472703385600 }, { target := 118, numerator := 387226613945562301422632960 }, { target := 226, numerator := 389706989307523698756943872 }, { target := 227, numerator := 18891134280418820019512672256 }, { target := 232, numerator := 18893770619436199626135306240 }, { target := 240, numerator := 387226945890128236206096384 }, { target := 624, numerator := 10613803055114547508543488 }, { target := 625, numerator := 514506499091463533729153024 }, { target := 630, numerator := 514578300685698993183784960 }, { target := 638, numerator := 10546258224966281814081536 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk2.Parent2
