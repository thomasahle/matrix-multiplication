import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 57; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent3

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
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected,
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected,
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
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 376082831817551930402243870720 }, { target := 19, numerator := 1367681819064879743111056588800 }, { target := 21, numerator := 376082830635807388180225720320 }, { target := 26, numerator := 3993430008841458787156949467136 }, { target := 28, numerator := 3993428105626831515841300791296 }, { target := 30, numerator := 3530473872529688384298287104 }, { target := 33, numerator := 12630037178497794918787842048 }, { target := 35, numerator := 3530472698855596694528065536 }, { target := 40, numerator := 51451882882798617675494850560 }, { target := 42, numerator := 51451882882798617675494850560 }, { target := 44, numerator := 896053900217571099216260890624 }, { target := 45, numerator := 2098695222850996247289921536 }, { target := 47, numerator := 2098695222850996247289921536 }, { target := 49, numerator := 21818693192404827345097064448 }, { target := 50, numerator := 375914382893250196543367020544 }, { target := 53, numerator := 1367069134016374816829949870080 }, { target := 55, numerator := 375914381711505654321348870144 }, { target := 60, numerator := 13689756987024798120878582792192 }, { target := 62, numerator := 13689750479805039334855597359104 }, { target := 64, numerator := 30596982207138605023184797302784 }, { target := 65, numerator := 42380103532410440348499705856 }, { target := 67, numerator := 42380103532410440348499705856 }, { target := 69, numerator := 539896599633336472390380552192 }, { target := 70, numerator := 17176418045084651314225348608 }, { target := 71, numerator := 3993428719635101593069238091776 }, { target := 73, numerator := 3993426816421089063102725488640 }, { target := 75, numerator := 30596997205374554617177996001280 }, { target := 76, numerator := 17640645559816668917312520192 }, { target := 77, numerator := 3565154362436659782965264384 }, { target := 80, numerator := 12754104341351407835475345408 }, { target := 82, numerator := 3565153177233353047126573056 }, { target := 87, numerator := 42447803378308859582283251712 }, { target := 89, numerator := 42447803378308859582283251712 }, { target := 91, numerator := 17640645559816668917312520192 }, { target := 92, numerator := 38047313394911609386352771072 }, { target := 94, numerator := 38047313394911609386352771072 }, { target := 96, numerator := 298498291972687318785051328512 }, { target := 97, numerator := 16247963015620616108051005440 }, { target := 98, numerator := 51451882882798617675494850560 }, { target := 100, numerator := 51451882882798617675494850560 }, { target := 102, numerator := 539896599633336472390380552192 }, { target := 103, numerator := 298498291972687318785051328512 }, { target := 104, numerator := 896046401099596302219661541376 }, { target := 105, numerator := 2098695222850996247289921536 }, { target := 107, numerator := 2098695222850996247289921536 }, { target := 109, numerator := 17176418045084651314225348608 }, { target := 110, numerator := 16247963015620616108051005440 }, { target := 111, numerator := 21818693192404827345097064448 }]

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
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot15.Left0.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1562754936854411272005961646080 }, { target := 2, numerator := 55639974629995987140555889967104 }, { target := 5, numerator := 55639799321585043570716621930496 }, { target := 12, numerator := 1562937782162261501798990741504 }, { target := 16, numerator := 39586771529594769837900439748608 }, { target := 19, numerator := 134663274036452297517162660102144 }, { target := 21, numerator := 39586770235666045035043176316928 }, { target := 26, numerator := 35996600894798833695955991134208 }, { target := 28, numerator := 35996422911029760165840951443456 }, { target := 44, numerator := 692028278120823763221346254848 }, { target := 50, numerator := 39586769619408660415407810674688 }, { target := 53, numerator := 134663267505396568918736660070400 }, { target := 55, numerator := 39586768325480552605699497000960 }, { target := 60, numerator := 122472824768100357439591985184768 }, { target := 62, numerator := 122472177402766088083521381859328 }, { target := 64, numerator := 25175966782786482461070753529856 }, { target := 71, numerator := 35996600894798833695955991134208 }, { target := 73, numerator := 35996422911029760165840951443456 }, { target := 75, numerator := 25175776499751421711586512863232 }, { target := 104, numerator := 692218561155884512705586921472 }]

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
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 23211375736600880154358579200 }, { target := 1, numerator := 22727805408755028484476108800 }, { target := 2, numerator := 17892102130296511785651404800 }, { target := 3, numerator := 562392291284725492073313075200 }, { target := 4, numerator := 17892102130296511785651404800 }, { target := 5, numerator := 17892102130296511785651404800 }, { target := 6, numerator := 18375672458142363455533875200 }, { target := 7, numerator := 18375672458142363455533875200 }, { target := 8, numerator := 310935720804882623734428467200 }, { target := 9, numerator := 16924961474604808445886464000 }, { target := 10, numerator := 562392291284725492073313075200 }, { target := 11, numerator := 310935720804882623734428467200 }, { target := 12, numerator := 23211375736600880154358579200 }, { target := 13, numerator := 17892102130296511785651404800 }, { target := 14, numerator := 16924961474604808445886464000 }, { target := 15, numerator := 22727805408755028484476108800 }, { target := 16, numerator := 2098695222850996247289921536 }, { target := 17, numerator := 51451882882798617675494850560 }, { target := 18, numerator := 2098695222850996247289921536 }, { target := 19, numerator := 43124801837293051920118710272 }, { target := 20, numerator := 42380103532410440348499705856 }, { target := 21, numerator := 2098695222850996247289921536 }, { target := 22, numerator := 42447803378308859582283251712 }, { target := 23, numerator := 38047313394911609386352771072 }, { target := 24, numerator := 51451882882798617675494850560 }, { target := 25, numerator := 2098695222850996247289921536 }, { target := 26, numerator := 3554750215464568363365171200 }, { target := 27, numerator := 3530473872529688384298287104 }, { target := 28, numerator := 3554750215464568363365171200 }, { target := 29, numerator := 3565154362436659782965264384 }, { target := 50, numerator := 2098695222850996247289921536 }, { target := 51, numerator := 51451882882798617675494850560 }, { target := 52, numerator := 2098695222850996247289921536 }, { target := 53, numerator := 43124801837293051920118710272 }, { target := 54, numerator := 42380103532410440348499705856 }, { target := 55, numerator := 2098695222850996247289921536 }, { target := 56, numerator := 42447803378308859582283251712 }, { target := 57, numerator := 38047313394911609386352771072 }, { target := 58, numerator := 51451882882798617675494850560 }, { target := 59, numerator := 2098695222850996247289921536 }, { target := 60, numerator := 12716884192495323960469094400 }, { target := 61, numerator := 12630037178497794918787842048 }, { target := 62, numerator := 12716884192495323960469094400 }, { target := 63, numerator := 12754104341351407835475345408 }, { target := 71, numerator := 3554749033720026141347020800 }, { target := 72, numerator := 3530472698855596694528065536 }, { target := 73, numerator := 3554749033720026141347020800 }, { target := 74, numerator := 3565153177233353047126573056 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent3
