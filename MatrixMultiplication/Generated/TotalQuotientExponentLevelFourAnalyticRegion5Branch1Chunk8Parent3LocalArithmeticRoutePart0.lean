import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk8Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 82; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk8.Parent3

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
  [{ target := 80, numerator := 13634165865388333034635264 }, { target := 82, numerator := 506031012651428676175396864 }, { target := 85, numerator := 506032375529059061174632448 }, { target := 92, numerator := 13633918069455535762046976 }, { target := 176, numerator := 506031012651428676175396864 }, { target := 178, numerator := 18781301936122292359307198464 }, { target := 181, numerator := 18781352519220241495016603648 }, { target := 188, numerator := 506021815724528833319141376 }, { target := 286, numerator := 506032375529059061174632448 }, { target := 288, numerator := 18781352519220241495016603648 }, { target := 291, numerator := 18781403102454424519453966336 }, { target := 298, numerator := 506023178577389420367839232 }, { target := 573, numerator := 13633918069455535762046976 }, { target := 575, numerator := 506021815724528833319141376 }, { target := 578, numerator := 506023178577389420367839232 }, { target := 585, numerator := 13633670278026338116829184 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk8.Parent3
