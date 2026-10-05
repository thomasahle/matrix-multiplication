import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk6Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 64; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk6.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
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
    Slot15.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 2165211703439374665853698048 }, { target := 37, numerator := 82514184179878432319584862208 }, { target := 40, numerator := 82522202461349293185910702080 }, { target := 47, numerator := 2163922164336536859640332288 }, { target := 86, numerator := 2874526592353480051922042880 }, { target := 89, numerator := 10314548902245703014930186240 }, { target := 91, numerator := 2875730536983333851585576960 }, { target := 122, numerator := 294626251764933647897985024 }, { target := 124, numerator := 294635360334023551512215552 }, { target := 145, numerator := 7827343576063492779159846912 }, { target := 147, numerator := 298079831242074222134529359872 }, { target := 150, numerator := 298108307611341378326657761280 }, { target := 157, numerator := 7822233777337430171484946432 }, { target := 161, numerator := 103431633502913228927014010880 }, { target := 164, numerator := 371257250913881055408097853440 }, { target := 166, numerator := 103477456795163440600831754240 }, { target := 197, numerator := 7842559756722400196252663808 }, { target := 199, numerator := 7842808850328023598909882368 }, { target := 216, numerator := 291357329913927329617281024 }, { target := 218, numerator := 13974825518336391865291505664 }, { target := 221, numerator := 13982785069072140284429598720 }, { target := 228, numerator := 297227456044395915770855424 }, { target := 232, numerator := 103447998644769982768333455360 }, { target := 235, numerator := 371314852869179657881418465280 }, { target := 237, numerator := 103493804956992966250903633920 }, { target := 242, numerator := 102589844995520839081430876160 }, { target := 244, numerator := 102592756889529559990839279616 }, { target := 406, numerator := 2851077672254147150468874240 }, { target := 409, numerator := 10231266275570620818805227520 }, { target := 411, numerator := 2852290051657447178848174080 }, { target := 416, numerator := 7823242858192550022164250624 }, { target := 418, numerator := 7823492068661517205505048576 }, { target := 498, numerator := 290255690162501761357578240 }, { target := 500, numerator := 290264821576663724762071040 }]

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
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot19.Left5.expected,
    Slot19.Left12.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 294626251764933647897985024 }, { target := 17, numerator := 7842559756722400196252663808 }, { target := 19, numerator := 102589844995520839081430876160 }, { target := 27, numerator := 7823242858192550022164250624 }, { target := 34, numerator := 290255690162501761357578240 }, { target := 35, numerator := 1000671351247282149638799360 }, { target := 37, numerator := 34892233228244050708298465280 }, { target := 40, numerator := 34908539615664373163486085120 }, { target := 47, numerator := 984382078901659586820833280 }, { target := 86, numerator := 291356462333176763570454528 }, { target := 89, numerator := 1034573946607194781727588352 }, { target := 91, numerator := 291357329913927329617281024 }, { target := 126, numerator := 294635360334023551512215552 }, { target := 127, numerator := 7842808850328023598909882368 }, { target := 129, numerator := 102592756889529559990839279616 }, { target := 137, numerator := 7823492068661517205505048576 }, { target := 144, numerator := 290264821576663724762071040 }, { target := 145, numerator := 3521779272789405017497927680 }, { target := 147, numerator := 122800301628898461549739376640 }, { target := 150, numerator := 122857690597973458332218818560 }, { target := 157, numerator := 3464450538790844862446960640 }, { target := 161, numerator := 13974783905209254100869316608 }, { target := 164, numerator := 49622881957091628276170883072 }, { target := 166, numerator := 13974825518336391865291505664 }, { target := 216, numerator := 2875730536983333851585576960 }, { target := 218, numerator := 103477456795163440600831754240 }, { target := 221, numerator := 103493804956992966250903633920 }, { target := 228, numerator := 2852290051657447178848174080 }, { target := 232, numerator := 13982743432243683581063331840 }, { target := 235, numerator := 49651145340135178777458114560 }, { target := 237, numerator := 13982785069072140284429598720 }, { target := 406, numerator := 297226570984049295992291328 }, { target := 409, numerator := 1055418040557654215126679552 }, { target := 411, numerator := 297227456044395915770855424 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk6.Parent1
