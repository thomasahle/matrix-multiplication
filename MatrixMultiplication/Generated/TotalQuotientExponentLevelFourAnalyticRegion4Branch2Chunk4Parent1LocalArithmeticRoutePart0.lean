import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk4Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 47; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 14339628823857928074745085952 }, { target := 19, numerator := 50533025905931242286604091392 }, { target := 21, numerator := 14355507784475167232194772992 }, { target := 26, numerator := 14339628823857928074745085952 }, { target := 28, numerator := 14339628669896745313550467072 }, { target := 50, numerator := 14339628669896745313550467072 }, { target := 53, numerator := 50533026220490787759830597632 }, { target := 55, numerator := 14355507623876804520162885632 }, { target := 60, numerator := 50533025905931242286604091392 }, { target := 62, numerator := 50533026220490787759830597632 }, { target := 71, numerator := 14355507784475167232194772992 }, { target := 73, numerator := 14355507623876804520162885632 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4.Parent1
