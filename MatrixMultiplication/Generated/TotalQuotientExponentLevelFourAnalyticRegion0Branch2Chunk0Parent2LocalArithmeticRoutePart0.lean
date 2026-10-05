import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk0Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0.Parent2

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
  [{ target := 80, numerator := 5911564550310430922244096 }, { target := 82, numerator := 336273390398395296314818560 }, { target := 85, numerator := 336274818105623792289054720 }, { target := 92, numerator := 5910300009622334487920640 }, { target := 176, numerator := 336273390398395296314818560 }, { target := 178, numerator := 19128572838487143535450521600 }, { target := 181, numerator := 19128654052173662009897779200 }, { target := 188, numerator := 336201458276050361804390400 }, { target := 286, numerator := 336274818105623792289054720 }, { target := 288, numerator := 19128654052173662009897779200 }, { target := 291, numerator := 19128735266204987330815590400 }, { target := 298, numerator := 336202885677878508047564800 }, { target := 573, numerator := 5910300009622334487920640 }, { target := 575, numerator := 336201458276050361804390400 }, { target := 578, numerator := 336202885677878508047564800 }, { target := 585, numerator := 5909035739431690672537600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0.Parent2
