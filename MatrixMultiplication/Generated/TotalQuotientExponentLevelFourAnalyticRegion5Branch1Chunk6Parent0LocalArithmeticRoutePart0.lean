import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk6Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 67; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk6.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 651764991312722814566400 }, { target := 72, numerator := 17858618108910312137687040 }, { target := 74, numerator := 190219576678120654362378240 }, { target := 82, numerator := 17906674264130128026009600 }, { target := 89, numerator := 603641113213510342410240 }, { target := 146, numerator := 17858618108910312137687040 }, { target := 147, numerator := 489333187591957791473926144 }, { target := 149, numerator := 5212091508460906683735998464 }, { target := 157, numerator := 490649945219771876832706560 }, { target := 164, numerator := 16540004847460637594353664 }, { target := 242, numerator := 190219576678120654362378240 }, { target := 243, numerator := 5212091508460906683735998464 }, { target := 245, numerator := 55516156642175729257764880384 }, { target := 253, numerator := 5226116842169426469307023360 }, { target := 260, numerator := 176174477843179617684291584 }, { target := 640, numerator := 17906674264130128026009600 }, { target := 641, numerator := 490649945219771876832706560 }, { target := 643, numerator := 5226116842169426469307023360 }, { target := 651, numerator := 491970246140161188849254400 }, { target := 658, numerator := 16584512716739139977871360 }, { target := 1017, numerator := 603641113213510342410240 }, { target := 1018, numerator := 16540004847460637594353664 }, { target := 1020, numerator := 176174477843179617684291584 }, { target := 1028, numerator := 16584512716739139977871360 }, { target := 1035, numerator := 559070521458572639862784 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk6.Parent0
