import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk0Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk0.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 15215219939212957396762624 }, { target := 82, numerator := 533754506904209076309196800 }, { target := 85, numerator := 533752739960242423908532224 }, { target := 92, numerator := 15218295730562315279400960 }, { target := 176, numerator := 533754506904209076309196800 }, { target := 178, numerator := 18724269171181772089589760000 }, { target := 181, numerator := 18724207186254218245491916800 }, { target := 188, numerator := 533862406592913916035072000 }, { target := 286, numerator := 533752739960242423908532224 }, { target := 288, numerator := 18724207186254218245491916800 }, { target := 291, numerator := 18724145201531859659416141824 }, { target := 298, numerator := 533860639291755518188584960 }, { target := 573, numerator := 15218295730562315279400960 }, { target := 575, numerator := 533862406592913916035072000 }, { target := 578, numerator := 533860639291755518188584960 }, { target := 585, numerator := 15221372143689896715878400 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk0.Parent0
