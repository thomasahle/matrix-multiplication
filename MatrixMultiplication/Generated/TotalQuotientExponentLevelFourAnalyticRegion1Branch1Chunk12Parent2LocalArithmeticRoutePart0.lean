import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk12Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 52; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12.Parent2

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
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 3960875442773949183697092608 }, { target := 2, numerator := 154495468475220657481971662848 }, { target := 5, numerator := 154495411806822863046229098496 }, { target := 12, numerator := 3960894332239880662277947392 }, { target := 16, numerator := 442168556461188499869024649216 }, { target := 19, numerator := 1590653050979343445534110121984 }, { target := 21, numerator := 442168701726992237322529931264 }, { target := 26, numerator := 4234887985070667502362675904512 }, { target := 28, numerator := 4234886976169574969013373501440 }, { target := 30, numerator := 3661520425567193567823134720 }, { target := 33, numerator := 13373770414294074264649728000 }, { target := 35, numerator := 3661519191941183638496870400 }, { target := 40, numerator := 33917618751812319469344129024 }, { target := 42, numerator := 33917626838403752781768818688 }, { target := 44, numerator := 16189934576279113907665108992 }, { target := 45, numerator := 1760195783527186239926042624 }, { target := 47, numerator := 1760196203190613916818341888 }, { target := 49, numerator := 18278958392573193121557381120 }, { target := 50, numerator := 442168556461188499869024649216 }, { target := 53, numerator := 1590653050979343445534110121984 }, { target := 55, numerator := 442168701726992237322529931264 }, { target := 60, numerator := 15457254832714040948707643359232 }, { target := 62, numerator := 15457251164817635517117014999040 }, { target := 64, numerator := 15667678622205594104192040960 }, { target := 65, numerator := 54633769127170742139242938368 }, { target := 67, numerator := 54633782152877901187400073216 }, { target := 69, numerator := 206291101859040322371861872640 }, { target := 70, numerator := 18278958392573193121557381120 }, { target := 71, numerator := 4234958532495824100282188431360 }, { target := 73, numerator := 4234957523610193550353555783680 }, { target := 75, numerator := 15667678622205594104192040960 }, { target := 76, numerator := 18278958392573193121557381120 }, { target := 77, numerator := 3661520425567193567823134720 }, { target := 80, numerator := 13373770414294074264649728000 }, { target := 82, numerator := 3661519191941183638496870400 }, { target := 87, numerator := 54633769127170742139242938368 }, { target := 89, numerator := 54633782152877901187400073216 }, { target := 91, numerator := 18278958392573193121557381120 }, { target := 92, numerator := 56935563613321677991453917184 }, { target := 94, numerator := 56935577187819473232470212608 }, { target := 96, numerator := 757793389360677234839421714432 }, { target := 97, numerator := 18801214346646712925030449152 }, { target := 98, numerator := 33917618751812319469344129024 }, { target := 100, numerator := 33917626838403752781768818688 }, { target := 102, numerator := 206291101859040322371861872640 }, { target := 103, numerator := 757793389360677234839421714432 }, { target := 104, numerator := 16189934576279113907665108992 }, { target := 105, numerator := 1692495945699217538390425600 }, { target := 107, numerator := 1692496349221744150786867200 }, { target := 109, numerator := 18278958392573193121557381120 }, { target := 110, numerator := 18801214346646712925030449152 }, { target := 111, numerator := 18278958392573193121557381120 }]

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
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot19.Left5.expected,
    Slot19.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1363254909673925368847978725376 }, { target := 2, numerator := 53937997316512351666227027902464 }, { target := 5, numerator := 53937999134623447571040435175424 }, { target := 12, numerator := 1363263509103290674471912865792 }, { target := 16, numerator := 38989218246501797198537473130496 }, { target := 19, numerator := 141240527446998691268021572337664 }, { target := 21, numerator := 38994546728564161286735470264320 }, { target := 26, numerator := 35096787888192701319654341083136 }, { target := 28, numerator := 35096800666692338624453538742272 }, { target := 44, numerator := 1360286510383023718650618052608 }, { target := 50, numerator := 38989230008793819028131787309056 }, { target := 53, numerator := 141240570431907028592958380179456 }, { target := 55, numerator := 38994558491173346868287537938432 }, { target := 60, numerator := 127039564457036833742617367805952 }, { target := 62, numerator := 127039611142478044980091293794304 }, { target := 64, numerator := 53822123608980484813253783846912 }, { target := 71, numerator := 35102122112650305906939715911680 }, { target := 73, numerator := 35102134891471912304499071385600 }, { target := 75, numerator := 53822125247641654369020672999424 }, { target := 104, numerator := 1360295015365059366881647919104 }]

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
    Slot20.Left0.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot22.Left0.expected,
    Slot22.Left3.expected,
    Slot22.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 14990680163221401766356582400 }, { target := 1, numerator := 16924961474604808445886464000 }, { target := 2, numerator := 14507109835375550096474112000 }, { target := 3, numerator := 191010279499111409603575808000 }, { target := 4, numerator := 16924961474604808445886464000 }, { target := 5, numerator := 14507109835375550096474112000 }, { target := 6, numerator := 16924961474604808445886464000 }, { target := 7, numerator := 16924961474604808445886464000 }, { target := 8, numerator := 701660545704330772999464550400 }, { target := 9, numerator := 17408531802450660115768934400 }, { target := 10, numerator := 191010279499111409603575808000 }, { target := 11, numerator := 701660545704330772999464550400 }, { target := 12, numerator := 14990680163221401766356582400 }, { target := 13, numerator := 16924961474604808445886464000 }, { target := 14, numerator := 17408531802450660115768934400 }, { target := 15, numerator := 16924961474604808445886464000 }, { target := 16, numerator := 1624796107871248836854808576 }, { target := 17, numerator := 33917618751812319469344129024 }, { target := 18, numerator := 1760195783527186239926042624 }, { target := 19, numerator := 36490212589275130127697575936 }, { target := 20, numerator := 54633769127170742139242938368 }, { target := 21, numerator := 1692495945699217538390425600 }, { target := 22, numerator := 54633769127170742139242938368 }, { target := 23, numerator := 56935563613321677991453917184 }, { target := 24, numerator := 33917618751812319469344129024 }, { target := 25, numerator := 1692495945699217538390425600 }, { target := 26, numerator := 3346698108602537672271986688 }, { target := 27, numerator := 3661520425567193567823134720 }, { target := 28, numerator := 3346698108602537672271986688 }, { target := 29, numerator := 3661520425567193567823134720 }, { target := 50, numerator := 1624796495252874384755392512 }, { target := 51, numerator := 33917626838403752781768818688 }, { target := 52, numerator := 1760196203190613916818341888 }, { target := 53, numerator := 36490221289220803890964856832 }, { target := 54, numerator := 54633782152877901187400073216 }, { target := 55, numerator := 1692496349221744150786867200 }, { target := 56, numerator := 54633782152877901187400073216 }, { target := 57, numerator := 56935577187819473232470212608 }, { target := 58, numerator := 33917626838403752781768818688 }, { target := 59, numerator := 1692496349221744150786867200 }, { target := 60, numerator := 12223876135681873486754611200 }, { target := 61, numerator := 13373770414294074264649728000 }, { target := 62, numerator := 12223876135681873486754611200 }, { target := 63, numerator := 13373770414294074264649728000 }, { target := 71, numerator := 3346696981045306166775644160 }, { target := 72, numerator := 3661519191941183638496870400 }, { target := 73, numerator := 3346696981045306166775644160 }, { target := 74, numerator := 3661519191941183638496870400 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12.Parent2
