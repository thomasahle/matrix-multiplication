import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk10Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 81; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk10.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 35384894737258181850497548288 }, { target := 19, numerator := 127305731140716948006627180544 }, { target := 21, numerator := 35380077916774134914383609856 }, { target := 26, numerator := 35384894737258181850497548288 }, { target := 28, numerator := 35384786884114742109599170560 }, { target := 50, numerator := 35384786884114742109599170560 }, { target := 53, numerator := 127305351815483946117135073280 }, { target := 55, numerator := 35379970076973734969477169152 }, { target := 60, numerator := 127305731140716948006627180544 }, { target := 62, numerator := 127305351815483946117135073280 }, { target := 71, numerator := 35380077916774134914383609856 }, { target := 73, numerator := 35379970076973734969477169152 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk10.Parent2
