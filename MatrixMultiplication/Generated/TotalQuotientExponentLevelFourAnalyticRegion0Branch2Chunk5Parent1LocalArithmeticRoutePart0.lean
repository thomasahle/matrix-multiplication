import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk5Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 57; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5.Parent1

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
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 21313207150564740181807595520 }, { target := 19, numerator := 76202779351682841779938263040 }, { target := 21, numerator := 21321704907859438090584064000 }, { target := 26, numerator := 21313207150564740181807595520 }, { target := 28, numerator := 21314844234028770888637218816 }, { target := 50, numerator := 21314844234028770888637218816 }, { target := 53, numerator := 76208609624951301006679867392 }, { target := 55, numerator := 21323342273705920832984842240 }, { target := 60, numerator := 76202779351682841779938263040 }, { target := 62, numerator := 76208609624951301006679867392 }, { target := 71, numerator := 21321704907859438090584064000 }, { target := 73, numerator := 21323342273705920832984842240 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5.Parent1
