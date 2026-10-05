import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk10Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 86; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk10.Parent0

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
    Slot11.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 7232857859859904691504676864 }, { target := 19, numerator := 25138439190921665955068116992 }, { target := 21, numerator := 7242505586728108841131573248 }, { target := 26, numerator := 7232857859859904691504676864 }, { target := 28, numerator := 7232959602989433227220877312 }, { target := 50, numerator := 7232959602989433227220877312 }, { target := 53, numerator := 25138792808194990430681563136 }, { target := 55, numerator := 7242607465570234447937142784 }, { target := 60, numerator := 25138439190921665955068116992 }, { target := 62, numerator := 25138792808194990430681563136 }, { target := 71, numerator := 7242505586728108841131573248 }, { target := 73, numerator := 7242607465570234447937142784 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk10.Parent0
