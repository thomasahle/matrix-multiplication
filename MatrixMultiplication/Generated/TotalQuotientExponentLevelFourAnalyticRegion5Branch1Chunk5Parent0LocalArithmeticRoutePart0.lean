import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk5Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 63; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 2249735009321256379117207552 }, { target := 21, numerator := 76978248055030242966790733824 }, { target := 24, numerator := 76978148885533386987752390656 }, { target := 31, numerator := 2249834178791090760391327744 }, { target := 35, numerator := 26753376420712476371933200384 }, { target := 38, numerator := 92087110313449296381043802112 }, { target := 40, numerator := 26751583089983907471739060224 }, { target := 71, numerator := 2249735009321256379117207552 }, { target := 73, numerator := 2249745220289907319782768640 }, { target := 90, numerator := 2249745220289907319782768640 }, { target := 92, numerator := 76978596743887268521397190656 }, { target := 95, numerator := 76978497573991843975336558592 }, { target := 102, numerator := 2249844390212353463607623680 }, { target := 106, numerator := 92087110313449296381043802112 }, { target := 109, numerator := 316937552734849800774757646336 }, { target := 111, numerator := 92081766608171473438240669696 }, { target := 116, numerator := 76978248055030242966790733824 }, { target := 118, numerator := 76978596743887268521397190656 }, { target := 140, numerator := 26751583089983907471739060224 }, { target := 143, numerator := 92081766608171473438240669696 }, { target := 145, numerator := 26749775963871744206701592576 }, { target := 150, numerator := 76978148885533386987752390656 }, { target := 152, numerator := 76978497573991843975336558592 }, { target := 232, numerator := 2249834178791090760391327744 }, { target := 234, numerator := 2249844390212353463607623680 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5.Parent0
