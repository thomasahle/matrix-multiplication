import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk1Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 34; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 347456759560419757829128192 }, { target := 37, numerator := 13946294393475177871329722368 }, { target := 40, numerator := 13946265420895537073318002688 }, { target := 47, numerator := 347480616694898609671372800 }, { target := 86, numerator := 347456759560419757829128192 }, { target := 89, numerator := 1230833691636919040781320192 }, { target := 91, numerator := 347636993877871478536404992 }, { target := 145, numerator := 1230833691636919040781320192 }, { target := 147, numerator := 49400714692399054055687585792 }, { target := 150, numerator := 49400612145389376933313118208 }, { target := 157, numerator := 1230918171394967354258489344 }, { target := 161, numerator := 13946294393475177871329722368 }, { target := 164, numerator := 49400714692399054055687585792 }, { target := 166, numerator := 13955240150414343998315429888 }, { target := 216, numerator := 347636993877871478536404992 }, { target := 218, numerator := 13955240150414343998315429888 }, { target := 221, numerator := 13955211109543244350764351488 }, { target := 228, numerator := 347660883246864663282974720 }, { target := 232, numerator := 13946265420895537073318002688 }, { target := 235, numerator := 49400612145389376933313118208 }, { target := 237, numerator := 13955211109543244350764351488 }, { target := 406, numerator := 347480616694898609671372800 }, { target := 409, numerator := 1230918171394967354258489344 }, { target := 411, numerator := 347660883246864663282974720 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1.Parent2
