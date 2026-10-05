import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk10Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 86; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk10.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 5178590304304993769512501248 }, { target := 38, numerator := 18291496868651862059045093376 }, { target := 40, numerator := 5175769022664480559141486592 }, { target := 106, numerator := 18291496868651862059045093376 }, { target := 109, numerator := 64607257530302961358957707264 }, { target := 111, numerator := 18281498716122443258634698752 }, { target := 140, numerator := 5175769022664480559141486592 }, { target := 143, numerator := 18281498716122443258634698752 }, { target := 145, numerator := 5172947979043148304975134720 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk10.Parent0
