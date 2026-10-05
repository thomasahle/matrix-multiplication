import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk8Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 74; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk8.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 42615912825374305938636275712 }, { target := 19, numerator := 152438475088562388511752192000 }, { target := 21, numerator := 42626288679104642526555930624 }, { target := 26, numerator := 42615912825374305938636275712 }, { target := 28, numerator := 42617295911103764162257354752 }, { target := 50, numerator := 42617295911103764162257354752 }, { target := 53, numerator := 152443332445741767626655268864 }, { target := 55, numerator := 42627670135699156795406680064 }, { target := 60, numerator := 152438475088562388511752192000 }, { target := 62, numerator := 152443332445741767626655268864 }, { target := 71, numerator := 42626288679104642526555930624 }, { target := 73, numerator := 42627670135699156795406680064 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk8.Parent1
