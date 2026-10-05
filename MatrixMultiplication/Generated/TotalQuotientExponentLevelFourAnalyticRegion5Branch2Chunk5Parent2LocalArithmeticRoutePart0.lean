import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk5Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 65; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 2204196100914028955624800256 }, { target := 21, numerator := 77007206740579801780774240256 }, { target := 24, numerator := 77007395603488739193620791296 }, { target := 31, numerator := 2204148897245182604697665536 }, { target := 35, numerator := 23118310072845046000792895488 }, { target := 38, numerator := 82156837011907767822951907328 }, { target := 40, numerator := 23114975581101821784720670720 }, { target := 71, numerator := 2204196100914028955624800256 }, { target := 73, numerator := 2205105818340255998274437120 }, { target := 90, numerator := 2205105818340255998274437120 }, { target := 92, numerator := 77039674697700102363058012160 }, { target := 95, numerator := 77039863624109794521828556800 }, { target := 102, numerator := 2205058574679444956297297920 }, { target := 106, numerator := 82156837011907767822951907328 }, { target := 109, numerator := 291992376281862540632696815616 }, { target := 111, numerator := 82143734050064888047018704896 }, { target := 116, numerator := 77007206740579801780774240256 }, { target := 118, numerator := 77039674697700102363058012160 }, { target := 140, numerator := 23114975581101821784720670720 }, { target := 143, numerator := 82143734050064888047018704896 }, { target := 145, numerator := 23111682987522496399023276032 }, { target := 150, numerator := 77007395603488739193620791296 }, { target := 152, numerator := 77039863624109794521828556800 }, { target := 232, numerator := 2204148897245182604697665536 }, { target := 234, numerator := 2205058574679444956297297920 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5.Parent2
