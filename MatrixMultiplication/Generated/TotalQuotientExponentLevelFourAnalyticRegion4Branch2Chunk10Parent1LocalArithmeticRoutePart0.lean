import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk10Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 80; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk10.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 1381553244035464133508857856 }, { target := 21, numerator := 58039790593002888675425517568 }, { target := 24, numerator := 58039729202158109526698491904 }, { target := 31, numerator := 1381463518921981972686307328 }, { target := 35, numerator := 17833706864991865826548121600 }, { target := 38, numerator := 63782475507661236605714169856 }, { target := 40, numerator := 17830759181452241056204587008 }, { target := 71, numerator := 1381553244035464133508857856 }, { target := 73, numerator := 1381545886389911107831595008 }, { target := 90, numerator := 1381545886389911107831595008 }, { target := 92, numerator := 58039505163695694302196793344 }, { target := 95, numerator := 58039443773011918840148262912 }, { target := 102, numerator := 1381456161577044222136025088 }, { target := 106, numerator := 63782475507661236605714169856 }, { target := 109, numerator := 228164974246209921020690694144 }, { target := 111, numerator := 63772087457401453088165855232 }, { target := 116, numerator := 58039790593002888675425517568 }, { target := 118, numerator := 58039505163695694302196793344 }, { target := 140, numerator := 17830759181452241056204587008 }, { target := 143, numerator := 63772087457401453088165855232 }, { target := 145, numerator := 17827812195618714807399612416 }, { target := 150, numerator := 58039729202158109526698491904 }, { target := 152, numerator := 58039443773011918840148262912 }, { target := 232, numerator := 1381463518921981972686307328 }, { target := 234, numerator := 1381456161577044222136025088 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk10.Parent1
