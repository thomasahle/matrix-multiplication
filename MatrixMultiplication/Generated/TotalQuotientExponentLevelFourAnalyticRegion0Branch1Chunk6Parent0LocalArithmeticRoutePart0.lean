import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk6Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 63; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6.Parent0

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
  [{ target := 19, numerator := 3268968861990624899421437952 }, { target := 21, numerator := 115493307631059116244093370368 }, { target := 24, numerator := 115520134156207964825661210624 }, { target := 31, numerator := 3295965318665225883504082944 }, { target := 35, numerator := 43617328394272669018720567296 }, { target := 38, numerator := 147906700608000009142693527552 }, { target := 40, numerator := 43636887282839073522406391808 }, { target := 71, numerator := 3268968861990624899421437952 }, { target := 73, numerator := 3271881783735980423519404032 }, { target := 90, numerator := 3271881783735980423519404032 }, { target := 92, numerator := 115596480121003128649225863168 }, { target := 95, numerator := 115623332735665059324802105344 }, { target := 102, numerator := 3298904477258925311036227584 }, { target := 106, numerator := 147906700608000009142693527552 }, { target := 109, numerator := 501346080592084796921041911808 }, { target := 111, numerator := 147971777996743607604396163072 }, { target := 116, numerator := 115493307631059116244093370368 }, { target := 118, numerator := 115596480121003128649225863168 }, { target := 140, numerator := 43636887282839073522406391808 }, { target := 143, numerator := 147971777996743607604396163072 }, { target := 145, numerator := 43656459466706555017948561408 }, { target := 150, numerator := 115520134156207964825661210624 }, { target := 152, numerator := 115623332735665059324802105344 }, { target := 232, numerator := 3295965318665225883504082944 }, { target := 234, numerator := 3298904477258925311036227584 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6.Parent0
