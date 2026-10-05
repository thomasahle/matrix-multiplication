import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk7Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 78; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk7.Parent3

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
  [{ target := 80, numerator := 8501965637207808955908096 }, { target := 82, numerator := 401863411052599878547931136 }, { target := 85, numerator := 401861062929797363099762688 }, { target := 92, numerator := 8501965637207808955908096 }, { target := 176, numerator := 401863411052599878547931136 }, { target := 178, numerator := 18994925177781395290404683776 }, { target := 181, numerator := 18994814188784349761197047808 }, { target := 188, numerator := 401863411052599878547931136 }, { target := 286, numerator := 401861062929797363099762688 }, { target := 288, numerator := 18994814188784349761197047808 }, { target := 291, numerator := 18994703200435822578330763264 }, { target := 298, numerator := 401861062929797363099762688 }, { target := 573, numerator := 8501965637207808955908096 }, { target := 575, numerator := 401863411052599878547931136 }, { target := 578, numerator := 401861062929797363099762688 }, { target := 585, numerator := 8501965637207808955908096 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk7.Parent3
