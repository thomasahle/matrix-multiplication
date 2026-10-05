import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk21Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 86; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left2.expected,
    Slot0.Left5.expected,
    Slot0.Left12.expected,
    Slot1.Left0.expected,
    Slot1.Left3.expected,
    Slot1.Left5.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot2.Left5.expected,
    Slot2.Left12.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot4.Left0.expected,
    Slot4.Left3.expected,
    Slot4.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 8123980539356244184274042880 }, { target := 17, numerator := 162479610787124883685480857600 }, { target := 18, numerator := 8414122701476110047998115840 }, { target := 19, numerator := 151164066464450115000242012160 }, { target := 20, numerator := 226310886453495373704776908800 }, { target := 21, numerator := 8123980539356244184274042880 }, { target := 22, numerator := 226601028615615239568500981760 }, { target := 23, numerator := 226601028615615239568500981760 }, { target := 24, numerator := 162189468625005017821756784640 }, { target := 25, numerator := 8414122701476110047998115840 }, { target := 26, numerator := 786028721365058813514399875072 }, { target := 27, numerator := 33416288713887804000206585856 }, { target := 28, numerator := 786028721365058813514399875072 }, { target := 29, numerator := 33416288713887804000206585856 }, { target := 44, numerator := 93705686723624709362754256896 }, { target := 50, numerator := 8123982476264371923776962560 }, { target := 51, numerator := 162479649525287438475539251200 }, { target := 52, numerator := 8414124707559528063911854080 }, { target := 53, numerator := 151164102504776349010278481920 }, { target := 54, numerator := 226310940410221789305215385600 }, { target := 55, numerator := 8123982476264371923776962560 }, { target := 56, numerator := 226601082641516945445350277120 }, { target := 57, numerator := 226601082641516945445350277120 }, { target := 58, numerator := 162189507293992282335404359680 }, { target := 59, numerator := 8414124707559528063911854080 }, { target := 60, numerator := 2915934897614557331776922976256 }, { target := 61, numerator := 119777172777926930332177661952 }, { target := 62, numerator := 2915934897614557331776922976256 }, { target := 63, numerator := 119777172777926930332177661952 }, { target := 64, numerator := 3669631876865837391632291332096 }, { target := 71, numerator := 785878508439708696286727241728 }, { target := 72, numerator := 33425999430456342108658728960 }, { target := 73, numerator := 785878508439708696286727241728 }, { target := 74, numerator := 33425999430456342108658728960 }, { target := 75, numerator := 3669632018536831877721647742976 }, { target := 104, numerator := 93705856728818092669981949952 }]

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
    Slot6.Left0.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot13.Left4.expected,
    Slot13.Left5.expected,
    Slot13.Left6.expected,
    Slot13.Left7.expected,
    Slot13.Left8.expected,
    Slot13.Left9.expected,
    Slot13.Left10.expected,
    Slot13.Left11.expected,
    Slot13.Left12.expected,
    Slot13.Left13.expected,
    Slot13.Left14.expected,
    Slot13.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 267735668057685044017829511168 }, { target := 1, numerator := 44411098909363017362006081536 }, { target := 2, numerator := 8956775625543983617281039007744 }, { target := 3, numerator := 464691742246749620690258755584 }, { target := 4, numerator := 41161506306238894140395880448 }, { target := 5, numerator := 8956772352944010988616905916416 }, { target := 6, numerator := 41161506306238894140395880448 }, { target := 7, numerator := 40078308771864186399859146752 }, { target := 8, numerator := 1514310153055841421270353707008 }, { target := 9, numerator := 40078308771864186399859146752 }, { target := 10, numerator := 464691742246749620690258755584 }, { target := 11, numerator := 1514310153055841421270353707008 }, { target := 12, numerator := 267736758924342586905873874944 }, { target := 13, numerator := 40078308771864186399859146752 }, { target := 14, numerator := 40078308771864186399859146752 }, { target := 15, numerator := 44411098909363017362006081536 }, { target := 16, numerator := 9538666335580328669974729064448 }, { target := 19, numerator := 34520517335930473142606798782464 }, { target := 21, numerator := 9538666980182972746037811216384 }, { target := 26, numerator := 9510285699624060573961475325952 }, { target := 28, numerator := 9510286159150474352175515435008 }, { target := 44, numerator := 261794354893524120242283872256 }, { target := 49, numerator := 44411098909363017362006081536 }, { target := 50, numerator := 9538666805214993561778321883136 }, { target := 53, numerator := 34520518975072481334538920787968 }, { target := 55, numerator := 9538667449818399309128383070208 }, { target := 60, numerator := 34418822325315777879373118439424 }, { target := 62, numerator := 34418823928005892755848416985088 }, { target := 64, numerator := 8725032422831152631058081513472 }, { target := 69, numerator := 464691742246749620690258755584 }, { target := 70, numerator := 41161506306238894140395880448 }, { target := 71, numerator := 9510286330059606327315528679424 }, { target := 73, numerator := 9510286789586779525016734138368 }, { target := 75, numerator := 8725029235233776694047562268672 }, { target := 76, numerator := 41161506306238894140395880448 }, { target := 91, numerator := 40078308771864186399859146752 }, { target := 96, numerator := 1514310153055841421270353707008 }, { target := 97, numerator := 40078308771864186399859146752 }, { target := 102, numerator := 464691742246749620690258755584 }, { target := 103, numerator := 1514310153055841421270353707008 }, { target := 104, numerator := 261795417425982765912456953856 }, { target := 109, numerator := 40078308771864186399859146752 }, { target := 110, numerator := 40078308771864186399859146752 }, { target := 111, numerator := 44411098909363017362006081536 }]

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
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left2.expected,
    Slot16.Left3.expected,
    Slot16.Left4.expected,
    Slot16.Left5.expected,
    Slot16.Left6.expected,
    Slot16.Left7.expected,
    Slot16.Left8.expected,
    Slot16.Left9.expected,
    Slot17.Left0.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left2.expected,
    Slot18.Left3.expected,
    Slot19.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 95679730360793878454983458816 }, { target := 2, numerator := 3746885995742932560133606080512 }, { target := 5, numerator := 3746886137413927046222962491392 }, { target := 12, numerator := 95679900365987261762211151872 }, { target := 16, numerator := 737503633724447764461933035520 }, { target := 19, numerator := 2735676289617151801261855604736 }, { target := 21, numerator := 737363635277800094276857626624 }, { target := 26, numerator := 8123980539356244184274042880 }, { target := 28, numerator := 8123982476264371923776962560 }, { target := 30, numerator := 33416288713887804000206585856 }, { target := 33, numerator := 119777172777926930332177661952 }, { target := 35, numerator := 33425999430456342108658728960 }, { target := 40, numerator := 162479610787124883685480857600 }, { target := 42, numerator := 162479649525287438475539251200 }, { target := 45, numerator := 8414122701476110047998115840 }, { target := 47, numerator := 8414124707559528063911854080 }, { target := 50, numerator := 737503633724447764461933035520 }, { target := 53, numerator := 2735676289617151801261855604736 }, { target := 55, numerator := 737363635277800094276857626624 }, { target := 60, numerator := 151164066464450115000242012160 }, { target := 62, numerator := 151164102504776349010278481920 }, { target := 65, numerator := 226310886453495373704776908800 }, { target := 67, numerator := 226310940410221789305215385600 }, { target := 71, numerator := 8123980539356244184274042880 }, { target := 73, numerator := 8123982476264371923776962560 }, { target := 77, numerator := 33416288713887804000206585856 }, { target := 80, numerator := 119777172777926930332177661952 }, { target := 82, numerator := 33425999430456342108658728960 }, { target := 87, numerator := 226601028615615239568500981760 }, { target := 89, numerator := 226601082641516945445350277120 }, { target := 92, numerator := 226601028615615239568500981760 }, { target := 94, numerator := 226601082641516945445350277120 }, { target := 98, numerator := 162189468625005017821756784640 }, { target := 100, numerator := 162189507293992282335404359680 }, { target := 105, numerator := 8414122701476110047998115840 }, { target := 107, numerator := 8414124707559528063911854080 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21.Parent0
