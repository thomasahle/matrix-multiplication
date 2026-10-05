import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk3Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 43; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3.Parent1

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
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left6.expected,
    Slot12.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 3216706922427375843016704 }, { target := 57, numerator := 112415735767044016499064832 }, { target := 59, numerator := 1356335313537262858759307264 }, { target := 67, numerator := 112418385365309187755606016 }, { target := 74, numerator := 3216801550936846245036032 }, { target := 110, numerator := 12625127544796638032691200 }, { target := 112, numerator := 450367598737992169449062400 }, { target := 115, numerator := 450367598737992169449062400 }, { target := 122, numerator := 12624906772713404796764160 }, { target := 152, numerator := 157310562975256107351539712 }, { target := 153, numerator := 5497604571151473026631991296 }, { target := 155, numerator := 66330528985450189127933755392 }, { target := 163, numerator := 5497734147704390014570856448 }, { target := 170, numerator := 157315190709288856920784896 }, { target := 206, numerator := 391314889825115838401740800 }, { target := 208, numerator := 13959110247055974341384601600 }, { target := 211, numerator := 13959110247055974341384601600 }, { target := 218, numerator := 391308047010806015396413440 }, { target := 257, numerator := 302522287815739545632112640 }, { target := 260, numerator := 1071358454675720862118707200 }, { target := 262, numerator := 302724641754164080693739520 }, { target := 283, numerator := 157310620384329407303516160 }, { target := 284, numerator := 5497606577452752674519777280 }, { target := 286, numerator := 66330553192179403804177858560 }, { target := 294, numerator := 5497736154052957458546032640 }, { target := 301, numerator := 157315248120051006733025280 }, { target := 302, numerator := 4593204063860711681635123200 }, { target := 304, numerator := 163850248436270896089818726400 }, { target := 307, numerator := 163850248436270896089818726400 }, { target := 314, numerator := 4593123743782653394692341760 }, { target := 353, numerator := 13991171115149756945752129536 }, { target := 356, numerator := 49563275042960147115520557056 }, { target := 358, numerator := 14000312736384194663281590272 }, { target := 660, numerator := 3216917422362809000263680 }, { target := 661, numerator := 112423092205069392087613440 }, { target := 663, numerator := 1356424071544383338321018880 }, { target := 671, numerator := 112425741976723148997918720 }, { target := 678, numerator := 3217012057064728889917440 }, { target := 679, numerator := 391317787194825483957043200 }, { target := 681, numerator := 13959213602957462010750566400 }, { target := 684, numerator := 13959213602957462010750566400 }, { target := 691, numerator := 391310944329850165143797760 }, { target := 695, numerator := 13988125637000599412683046912 }, { target := 698, numerator := 49552456754187724417126105088 }, { target := 700, numerator := 13997265708930618695234879488 }, { target := 966, numerator := 12626737194635330007859200 }, { target := 968, numerator := 450425018683263096874598400 }, { target := 971, numerator := 450425018683263096874598400 }, { target := 978, numerator := 12626516394404599100866560 }, { target := 982, numerator := 304403111709562603873239040 }, { target := 985, numerator := 1078104069181050590330880000 }, { target := 987, numerator := 304605468779396254840913920 }]

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
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 155991313490005599201525760 }, { target := 15, numerator := 7046707757651193384772042752 }, { target := 20, numerator := 7045514362716133074447368192 }, { target := 28, numerator := 155991313490005599201525760 }, { target := 56, numerator := 20855880159196113115545600 }, { target := 57, numerator := 695670492551332228182835200 }, { target := 59, numerator := 8519926393278797460170342400 }, { target := 67, numerator := 695671085907620008663449600 }, { target := 74, numerator := 22742753154338041469337600 }, { target := 110, numerator := 24072587081623488958562304 }, { target := 112, numerator := 883393394426490782006378496 }, { target := 115, numerator := 883394253214244550589022208 }, { target := 122, numerator := 24072708539483314490179584 }, { target := 136, numerator := 545822029315549294955069440 }, { target := 137, numerator := 24656810960959235485794828288 }, { target := 142, numerator := 24652635207639027364709531648 }, { target := 150, numerator := 545822029315549294955069440 }, { target := 152, numerator := 726082831451234674654838784 }, { target := 153, numerator := 24219279988815198819585097728 }, { target := 155, numerator := 296615258246977765629059137536 }, { target := 163, numerator := 24219300646097950853346361344 }, { target := 170, numerator := 791772990602702035473137664 }, { target := 206, numerator := 808086228318376244681900032 }, { target := 208, numerator := 29716884559966671846217089024 }, { target := 211, numerator := 29716913297122612448273104896 }, { target := 218, numerator := 808090614661439292029534208 }, { target := 267, numerator := 156193423467030944719831040 }, { target := 268, numerator := 7055837816954748490752196608 }, { target := 273, numerator := 7054642875798828115315130368 }, { target := 281, numerator := 156193423467030944719831040 }, { target := 283, numerator := 726083632829915143285506048 }, { target := 284, numerator := 24219306719669859773753327616 }, { target := 286, numerator := 296615585621671071250479316992 }, { target := 294, numerator := 24219327376975411280628154368 }, { target := 301, numerator := 791773864483707005234577408 }, { target := 302, numerator := 9876261706816060318929649664 }, { target := 304, numerator := 362945787232427954756992892928 }, { target := 307, numerator := 362946138813850475054657175552 }, { target := 314, numerator := 9876314089857257951666896896 }, { target := 660, numerator := 20855791117120505489915904 }, { target := 661, numerator := 695667522456369899941920768 }, { target := 663, numerator := 8519890018312874613345878016 }, { target := 671, numerator := 695668115810124405632139264 }, { target := 678, numerator := 22742656056448600384733184 }, { target := 679, numerator := 695671085907620008663449600 }, { target := 681, numerator := 24219300646097950853346361344 }, { target := 684, numerator := 24219327376975411280628154368 }, { target := 691, numerator := 695668115810124405632139264 }, { target := 966, numerator := 22742753154338041469337600 }, { target := 968, numerator := 791772990602702035473137664 }, { target := 971, numerator := 791773864483707005234577408 }, { target := 978, numerator := 22742656056448600384733184 }]

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
    Slot18.Left11.expected,
    Slot18.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot19.Left5.expected,
    Slot19.Left12.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 146530974325733946430586880 }, { target := 15, numerator := 6944463357498563560980086784 }, { target := 20, numerator := 6942611274284466338235678720 }, { target := 28, numerator := 148411798219557004671713280 }, { target := 56, numerator := 12625127544796638032691200 }, { target := 57, numerator := 391314889825115838401740800 }, { target := 59, numerator := 4593204063860711681635123200 }, { target := 67, numerator := 391317787194825483957043200 }, { target := 74, numerator := 12626737194635330007859200 }, { target := 136, numerator := 525536425360171567163637760 }, { target := 137, numerator := 24906464082000911629725728768 }, { target := 142, numerator := 24899821546548697052416573440 }, { target := 150, numerator := 532282039865501295375810560 }, { target := 152, numerator := 450367598737992169449062400 }, { target := 153, numerator := 13959110247055974341384601600 }, { target := 155, numerator := 163850248436270896089818726400 }, { target := 163, numerator := 13959213602957462010750566400 }, { target := 170, numerator := 450425018683263096874598400 }, { target := 267, numerator := 146531218287133135973908480 }, { target := 268, numerator := 6944474919429446172529393664 }, { target := 273, numerator := 6942622833131790579919749120 }, { target := 281, numerator := 148412045312365310121082880 }, { target := 283, numerator := 450367598737992169449062400 }, { target := 284, numerator := 13959110247055974341384601600 }, { target := 286, numerator := 163850248436270896089818726400 }, { target := 294, numerator := 13959213602957462010750566400 }, { target := 301, numerator := 450425018683263096874598400 }, { target := 660, numerator := 12624906772713404796764160 }, { target := 661, numerator := 391308047010806015396413440 }, { target := 663, numerator := 4593123743782653394692341760 }, { target := 671, numerator := 391310944329850165143797760 }, { target := 678, numerator := 12626516394404599100866560 }, { target := 679, numerator := 112418385365309187755606016 }, { target := 681, numerator := 5497734147704390014570856448 }, { target := 684, numerator := 5497736154052957458546032640 }, { target := 691, numerator := 112425741976723148997918720 }, { target := 966, numerator := 3216801550936846245036032 }, { target := 968, numerator := 157315190709288856920784896 }, { target := 971, numerator := 157315248120051006733025280 }, { target := 978, numerator := 3217012057064728889917440 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3.Parent1
