import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk0Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0.Parent2

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
  [{ target := 80, numerator := 8102120858137514318233600 }, { target := 82, numerator := 392496944209362720108052480 }, { target := 85, numerator := 392494174416778893774028800 }, { target := 92, numerator := 8103457999384878755348480 }, { target := 176, numerator := 392496944209362720108052480 }, { target := 178, numerator := 19014015454849796358289752064 }, { target := 181, numerator := 19013881275769493735174307840 }, { target := 188, numerator := 392561720317095020922404864 }, { target := 286, numerator := 392494174416778893774028800 }, { target := 288, numerator := 19013881275769493735174307840 }, { target := 291, numerator := 19013747097636072933713510400 }, { target := 298, numerator := 392558950067395832410275840 }, { target := 573, numerator := 8103457999384878755348480 }, { target := 575, numerator := 392561720317095020922404864 }, { target := 578, numerator := 392558950067395832410275840 }, { target := 585, numerator := 8104795361308624933617664 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0.Parent2
