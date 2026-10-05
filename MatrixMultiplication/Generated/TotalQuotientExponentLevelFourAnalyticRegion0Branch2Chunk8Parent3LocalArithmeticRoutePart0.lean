import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk8Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 78; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk8.Parent3

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
  [{ target := 80, numerator := 8253440276926564468260864 }, { target := 82, numerator := 395872613982742575688187904 }, { target := 85, numerator := 396098088580028573857873920 }, { target := 92, numerator := 8419726587451723443339264 }, { target := 176, numerator := 395872613982742575688187904 }, { target := 178, numerator := 18987854911805027395351609344 }, { target := 181, numerator := 18998669701180053060184965120 }, { target := 188, numerator := 403848463350814089941090304 }, { target := 286, numerator := 396098088580028573857873920 }, { target := 288, numerator := 18998669701180053060184965120 }, { target := 291, numerator := 19009490650264522968373657600 }, { target := 298, numerator := 404078480700896719059025920 }, { target := 573, numerator := 8419726587451723443339264 }, { target := 575, numerator := 403848463350814089941090304 }, { target := 578, numerator := 404078480700896719059025920 }, { target := 585, numerator := 8589363153887181001457664 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk8.Parent3
