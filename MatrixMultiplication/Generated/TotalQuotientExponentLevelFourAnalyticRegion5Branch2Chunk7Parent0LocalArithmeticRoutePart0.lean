import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk7Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 73; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk7.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot21.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 2052478813904008844809338880 }, { target := 21, numerator := 77167412451416360554984374272 }, { target := 24, numerator := 77167431389082067045497962496 }, { target := 31, numerator := 2052431590137849156741365760 }, { target := 35, numerator := 15524022201981965009896341504 }, { target := 38, numerator := 54861384648549043755250876416 }, { target := 40, numerator := 15523657532242399219440156672 }, { target := 71, numerator := 2052478813904008844809338880 }, { target := 73, numerator := 2052820763015542698458218496 }, { target := 90, numerator := 1490455858494006310438174720 }, { target := 92, numerator := 57939010472805055659927142400 }, { target := 95, numerator := 57938972645720705486920089600 }, { target := 102, numerator := 1490408634930508605601873920 }, { target := 106, numerator := 54861384648549043755250876416 }, { target := 109, numerator := 193829076745080621700868997120 }, { target := 111, numerator := 54861263286575357889978826752 }, { target := 116, numerator := 77167412451416360554984374272 }, { target := 118, numerator := 77183641334391660306707251200 }, { target := 140, numerator := 15523657532242399219440156672 }, { target := 143, numerator := 54861263286575357889978826752 }, { target := 145, numerator := 15523265203789837121158643712 }, { target := 150, numerator := 77167431389082067045497962496 }, { target := 152, numerator := 77183660175657816773355372544 }, { target := 232, numerator := 2052431590137849156741365760 }, { target := 234, numerator := 2052773539452044993621917696 }]

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
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 90, numerator := 562364904521536388020043776 }, { target := 92, numerator := 19244630861586604646780108800 }, { target := 95, numerator := 19244687529937111286435282944 }, { target := 102, numerator := 562364904521536388020043776 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk7.Parent0
