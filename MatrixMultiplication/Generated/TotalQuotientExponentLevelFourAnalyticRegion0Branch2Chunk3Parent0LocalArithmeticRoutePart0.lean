import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk3Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 44; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk3.Parent0

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
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 181272239855939047483506688 }, { target := 82, numerator := 6367408952670709203096043520 }, { target := 85, numerator := 6369918524715369506071904256 }, { target := 92, numerator := 178661771772248370209357824 }, { target := 131, numerator := 224085396744606287872917504 }, { target := 134, numerator := 804678439879571449395019776 }, { target := 136, numerator := 224231107008590966572449792 }, { target := 176, numerator := 6922211260953116259657973760 }, { target := 178, numerator := 244023523444280482965005271040 }, { target := 181, numerator := 244111048128949129208943083520 }, { target := 188, numerator := 6828889237992645186792980480 }, { target := 227, numerator := 5478803477337588228981522432 }, { target := 230, numerator := 19660066577147087065033211904 }, { target := 232, numerator := 5482139534429304552538767360 }, { target := 286, numerator := 6924726574528292156268871680 }, { target := 288, numerator := 244111240739324427180032655360 }, { target := 291, numerator := 244198806304840259802507509760 }, { target := 298, numerator := 6831363688625257973431664640 }, { target := 302, numerator := 73672068085280538903642636288 }, { target := 305, numerator := 264304307230949376953684066304 }, { target := 307, numerator := 73715964551284704420909023232 }, { target := 573, numerator := 178760313486456592216883200 }, { target := 575, numerator := 6279811053355875141146378240 }, { target := 578, numerator := 6282279787485038413401292800 }, { target := 585, numerator := 176190662601141709805977600 }, { target := 589, numerator := 5468289214709868719580905472 }, { target := 592, numerator := 19622726762408965789502668800 }, { target := 594, numerator := 5471625162066876522628644864 }, { target := 763, numerator := 221742423552685459013369856 }, { target := 766, numerator := 796358992929943026514526208 }, { target := 768, numerator := 221888129856317215393972224 }]

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
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 224085396744606287872917504 }, { target := 27, numerator := 5478803477337588228981522432 }, { target := 29, numerator := 73672068085280538903642636288 }, { target := 37, numerator := 5468289214709868719580905472 }, { target := 44, numerator := 221742423552685459013369856 }, { target := 80, numerator := 27320319983053263788310528 }, { target := 82, numerator := 1554088862480223327831982080 }, { target := 85, numerator := 1554095460635076019051560960 }, { target := 92, numerator := 27314475903040880136683520 }, { target := 157, numerator := 804678439879571449395019776 }, { target := 158, numerator := 19660066577147087065033211904 }, { target := 160, numerator := 264304307230949376953684066304 }, { target := 168, numerator := 19622726762408965789502668800 }, { target := 175, numerator := 796358992929943026514526208 }, { target := 176, numerator := 999286554197816271270051840 }, { target := 178, numerator := 56843408322756709022328422400 }, { target := 181, numerator := 56843649661343918078086348800 }, { target := 188, numerator := 999072797163431107598745600 }, { target := 267, numerator := 224231107008590966572449792 }, { target := 268, numerator := 5482139534429304552538767360 }, { target := 270, numerator := 73715964551284704420909023232 }, { target := 278, numerator := 5471625162066876522628644864 }, { target := 285, numerator := 221888129856317215393972224 }, { target := 286, numerator := 999287410822153368854593536 }, { target := 288, numerator := 56843457050968620106996776960 }, { target := 291, numerator := 56843698389762713270637035520 }, { target := 298, numerator := 999073653604527995344650240 }, { target := 573, numerator := 27215934188832658129158144 }, { target := 575, numerator := 1548150981800201153245347840 }, { target := 578, numerator := 1548157554744747555375022080 }, { target := 585, numerator := 27210112437948701957160960 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk3.Parent0
